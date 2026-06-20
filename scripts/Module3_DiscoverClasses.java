//@category PCodeWorkshop

import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.ArrayDataType;
import ghidra.program.model.data.CategoryPath;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.DataTypeConflictHandler;
import ghidra.program.model.data.DataTypeManager;
import ghidra.program.model.data.PointerDataType;
import ghidra.program.model.data.StructureDataType;
import ghidra.program.model.data.TerminatedStringDataType;
import ghidra.program.model.data.UnsignedLongDataType;
import ghidra.program.model.listing.Data;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.GhidraClass;
import ghidra.program.model.listing.Listing;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.scalar.Scalar;
import ghidra.program.model.symbol.Namespace;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.SymbolTable;

/**
 * Module 3 — Discover classes from the {@code classmeta} section.
 *
 * The real lesson: what IS a class to Ghidra? Not one thing the tool detects —
 * two independent objects you assemble, plus a brittle auto-link between them.
 *
 *   1. A STRUCT {@link DataType} — the memory layout. A DataType pulls double
 *      duty: it parses bytes in the Listing ({@link Listing#createData(Address, DataType)
 *      createData} turns a raw {@code classmeta} chunk into named fields) AND it
 *      structures decompiler output (assigned to a variable, field accesses read
 *      as {@code obj->field}). That double duty pays off twice here: the
 *      {@code KlassChunk_<C>} type you build to PARSE the metadata is reused as the
 *      pointee of the instance struct's first field ({@code _klass}) — so the very
 *      type that decoded the data also makes dispatch legible as
 *      {@code obj->_klass->methods[N]}.
 *
 *   2. A CLASS NAMESPACE — a {@link GhidraClass} holding the methods, each taking
 *      the instance as its first argument.
 *
 * Those two are unrelated objects until something correlates them. Ghidra's
 * {@code __thiscall} tries to, automatically — but the link is BRITTLE, and worth
 * understanding rather than trusting: it only fires when the calling convention
 * is actually set to {@code __thiscall} (auto-analysis won't do that for stripped
 * C — the convention reads {@code unknown} and the receiver stays a bare
 * {@code long}); it then resolves the type purely BY NAME, picking any struct
 * whose name equals the class (category is only a tiebreak — see
 * {@link ghidra.program.model.listing.VariableUtilities#findOrCreateClassStruct(Function)
 * VariableUtilities.findOrCreateClassStruct} ->
 * {@link ghidra.program.database.data.DataTypeUtilities#findExistingClassStruct(DataTypeManager, GhidraClass)
 * DataTypeUtilities.findExistingClassStruct}); and when no such struct
 * exists it fabricates an empty placeholder. On x86 it also historically misfired
 * by reserving a register for the implicit {@code this} (on AArch64 the first arg
 * is {@code x0} either way, so it doesn't). This module DOES use it — one
 * {@link Function#setCallingConvention(String) setCallingConvention("__thiscall")}
 * call is far less code than pinning the receiver's storage by hand — but treat it
 * as the brittle convenience it is. When a receiver comes out wrong (a name that
 * doesn't match, a convention analysis never set, a silently-fabricated
 * placeholder), you now know why: the class&lt;-&gt;struct link is not intrinsic,
 * just a name match you can always override explicitly.
 *
 * No dataflow here — {@code classmeta} is one contiguous section of fixed-shape
 * chunks, which is why you parse it BEFORE {@code rt_alloc} (whose sites drag in
 * relocated-pointer indirection and runtime-owned classes). Build the type
 * universe first; connect allocations to it later. The payoff lands next: type an
 * {@code rt_alloc} result as {@code <C> *} and the decompiler PROPAGATES it through
 * every field/dispatch — a {@code decompile}-pipeline action (recall {@code
 * normalize} does none).
 *
 * Each chunk (emitted by {@code KLASS_DEFINE} in {@code miniobj.h}) is:
 * <pre>
 *     char *   name;            // slot 0
 *     uint64_t instance_size;   // slot 1
 *     uint64_t method_count;    // slot 2
 *     void *   methods[count];  // slots 3 .. 3+count
 * </pre>
 *
 * {@link #run} below is just the walk + orchestration; it assembles each class
 * from four pieces, each its own function you fill in:
 * (A) {@link #buildAndApplyChunkStruct} — the chunk layout struct;
 * (B) {@link #buildInstanceStruct} — the instance struct that reuses it;
 * (C) {@link #defineClass} — the class namespace;
 * (D) {@link #linkMethodToClass} — the {@code __thiscall} link.
 *
 * Runs on both programs: {@code sysmond} (the app's classes) and, re-run,
 * {@code libminiobj_rt.so} (the runtime's — StringObject/File/Codec).
 */
public class Module3_DiscoverClasses extends GhidraScript {

    @Override
    public void run() throws Exception {
        // --- Step 1: find the classmeta section ---
        // The section header survives stripping, so you can always locate it by
        // name and walk it start-to-end. Pitfall: if the importer wasn't ELF-
        // section-aware, classmeta can be merged into .rodata and no block by
        // this exact name exists — re-import with ELF sections enabled.
        MemoryBlock block = currentProgram.getMemory().getBlock("classmeta");
        if (block == null) {
            printerr("ERROR: `classmeta` section not found (re-import with ELF sections enabled?)");
            return;
        }
        println("classmeta section: " + block.getStart() + " .. " + block.getEnd()
            + " (" + block.getSize() + " bytes)");

        int txId = currentProgram.startTransaction("Module3: discover classes from classmeta");
        boolean success = false;
        try {
            int classCount = 0;
            int methodCount = 0;

            // --- Step 2: walk the section, assembling one class per chunk ---
            Address cursor = block.getStart();
            Address end = block.getEnd();
            while (cursor.compareTo(end) < 0) {
                // Peek (raw) just enough to learn the class name and method count —
                // the count is needed to size the struct before it can be applied.
                long namePtr = getLong(cursor);
                if (namePtr == 0L) break;
                String className = typeAndReadString(toAddr(namePtr));
                if (className == null || className.isEmpty()) {
                    printerr("  WARN: bad class name pointer at " + cursor);
                    break;
                }
                int count = (int) getLong(cursor.add(16));

                // (A) stamp the chunk struct on the bytes, then read fields by index.
                Data chunk = buildAndApplyChunkStruct(cursor, className, count);
                DataType chunkType = chunk.getDataType();
                long instanceSize = ((Scalar) chunk.getComponent(1).getValue()).getUnsignedValue();
                long structCount  = ((Scalar) chunk.getComponent(2).getValue()).getUnsignedValue();
                Data methodsArr = chunk.getComponent(3);

                buildInstanceStruct(className, instanceSize, chunkType); // (B) reuse the chunk type
                GhidraClass cls = defineClass(className);                // (C) the class namespace
                classCount++;
                println("  " + className + " (size=" + instanceSize
                    + ", " + structCount + " methods) @ " + cursor);

                // --- Step 3: force a function at each method slot, link it to the class ---
                for (int i = 0; i < structCount; i++) {
                    Address fnAddr = (Address) methodsArr.getComponent(i).getValue();
                    // Slot 0 is the "init" method by convention and is usually null
                    // (most classes rely on the runtime's zero-init) — skip empties.
                    if (fnAddr == null || fnAddr.getOffset() == 0L) continue;
                    Function method = forceFunctionAt(fnAddr);
                    if (method == null) {
                        printerr("    WARN: could not create function at " + fnAddr);
                        continue;
                    }
                    linkMethodToClass(method, cls);                      // (D) the __thiscall link
                    methodCount++;
                    println("    [" + i + "] " + fnAddr + " -> " + className + "::" + method.getName());
                }

                cursor = cursor.add(chunkType.getLength());
            }

            success = true;
            println("\nDiscovered " + classCount + " class(es), "
                + methodCount + " method function(s)");
        } finally {
            currentProgram.endTransaction(txId, success);
        }
    }

    /**
     * EXERCISE A — describe one class's metadata chunk as a Ghidra struct and
     * stamp it onto memory.
     *
     * Build a {@link StructureDataType} in category {@code /MiniObj} named
     * {@code "KlassChunk_<className>"} with the four fields above (the
     * {@code methods[]} field is an {@link ArrayDataType} of {@code methodCount}
     * 8-byte pointers), register it with the {@link DataTypeManager}, then clear
     * the raw bytes at {@code cursor} and {@link Listing#createData(Address, DataType)
     * createData} there with that type.
     * Return the applied {@link Data} so the caller reads fields by component
     * index instead of raw {@code getLong()}s — and so the listing now renders
     * the chunk as named fields instead of opaque bytes.
     */
    private Data buildAndApplyChunkStruct(Address cursor, String className, int methodCount) throws Exception {
        DataTypeManager dtm = currentProgram.getDataTypeManager();
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        CategoryPath cat = new CategoryPath("/MiniObj");
        StructureDataType s = new StructureDataType(cat, "KlassChunk_" + className, 0);
        s.add(new PointerDataType(), 8, "name", null);
        s.add(new UnsignedLongDataType(), 8, "instance_size", null);
        s.add(new UnsignedLongDataType(), 8, "method_count", null);
        s.add(new ArrayDataType(new PointerDataType(), methodCount, 8), 8 * methodCount, "methods", null);
        DataType chunkType = dtm.addDataType(s, DataTypeConflictHandler.REPLACE_HANDLER);

        Listing listing = currentProgram.getListing();
        listing.clearCodeUnits(cursor, cursor.add(chunkType.getLength() - 1), false);
        return listing.createData(cursor, chunkType);
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * EXERCISE B — build the per-class INSTANCE struct, reusing the chunk type.
     *
     * This is the layout of an object of the class. Its payload fields are still
     * unknown, but two things are: the object is {@code instanceSize} bytes, and
     * its first 8 bytes are the {@code _klass} pointer every object shares.
     * Build a {@link StructureDataType} named exactly {@code className} (so the
     * {@code __thiscall} link can find it later BY NAME) in {@code /MiniObj}, sized
     * to the instance, and set its offset-0 field {@code _klass} to a POINTER TO
     * {@code chunkType} — the very type built in {@link #buildAndApplyChunkStruct}.
     * That one reuse is what later renders dispatch as {@code obj->_klass->methods[N]}.
     * Register it with the {@link DataTypeManager} (REPLACE handler) and return it.
     * (External classes from another module read size 0 — fall back to 16 bytes.)
     */
    private DataType buildInstanceStruct(String className, long instanceSize, DataType chunkType) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        DataTypeManager dtm = currentProgram.getDataTypeManager();
        CategoryPath cat = new CategoryPath("/MiniObj");
        int size = instanceSize > 0 ? (int) instanceSize : 16;
        StructureDataType s = new StructureDataType(cat, className, size);
        s.replaceAtOffset(0, new PointerDataType(chunkType), 8, "_klass", null);
        return dtm.addDataType(s, DataTypeConflictHandler.REPLACE_HANDLER);
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * EXERCISE C — define the class namespace.
     *
     * The metadata is authoritative: this name IS a class. Return the
     * {@link GhidraClass} for {@code className} from the {@link SymbolTable}:
     * create it under the global namespace if absent; if Module 2's logging pass
     * already made a *plain* {@link Namespace} for it (a guess), promote that with
     * {@link SymbolTable#convertNamespaceToClass}; if it is already a GhidraClass,
     * return it as-is.
     */
    private GhidraClass defineClass(String className) throws Exception {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        SymbolTable symTab = currentProgram.getSymbolTable();
        Namespace global = currentProgram.getGlobalNamespace();
        Namespace ns = symTab.getNamespace(className, global);
        if (ns == null) return symTab.createClass(global, className, SourceType.ANALYSIS);
        if (ns instanceof GhidraClass cls) return cls;
        return symTab.convertNamespaceToClass(ns);
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * EXERCISE D — link a method to its class.
     *
     * The two halves now exist (a struct named like the class, and the class
     * namespace). Tie them together for this method: put it in {@code cls}
     * ({@link Function#setParentNamespace}), then set its calling convention to
     * {@code __thiscall} ({@link Function#setCallingConvention(String)}) so Ghidra
     * types the receiver as {@code <Class> *this}, matching the struct BY NAME.
     * setParentNamespace ALONE does nothing — on AArch64 the convention stays
     * {@code unknown}; the convention is what turns the link on.
     */
    private void linkMethodToClass(Function method, GhidraClass cls) throws Exception {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        method.setParentNamespace(cls);
        method.setCallingConvention("__thiscall");
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    // ============================ PROVIDED HELPERS ============================

    /** Apply a {@link TerminatedStringDataType} at addr (if not already a string)
     *  and read it — same as a manual "Data → C string" action. */
    private String typeAndReadString(Address addr) {
        Listing listing = currentProgram.getListing();
        Data data = listing.getDataAt(addr);
        if (data == null || !(data.getValue() instanceof String)) {
            try {
                listing.clearCodeUnits(addr, addr, false);
                data = listing.createData(addr, TerminatedStringDataType.dataType);
            } catch (Exception e) {
                return null;
            }
        }
        Object v = data.getValue();
        return (v instanceof String) ? (String) v : null;
    }

    /** Ensure a {@link Function} exists at addr, disassembling first if needed. */
    private Function forceFunctionAt(Address addr) {
        Function f = getFunctionAt(addr);
        if (f == null) {
            if (currentProgram.getListing().getInstructionAt(addr) == null) disassemble(addr);
            f = createFunction(addr, null);
        }
        return f;
    }
}
