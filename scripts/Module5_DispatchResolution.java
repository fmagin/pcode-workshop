//Resolve indirect dispatch CALLINDs — type-driven.
//
//Every method call shapes as LOAD(obj->_klass) → LOAD(klass->methods[S]) → CALLIND.
//The concrete target depends only on the OBJECT'S TYPE at the call site: if `obj`
//is a `CpuConfig *` (typed by the allocation-typing script or any other source of
//type information), then the method at slot S is `klass_CpuConfig`'s methods[S].
//You do not trace where the object came from — you read its data type and map
//type → klass_<name> global → chunk → method. This keeps the concern clean:
//"the method target is a function of the receiver's type."
//
//Scope: this resolves WHICH method each CALLIND calls — it turns the opaque
//(**(code **)(...))() into a named Class::method(...) call and makes the call
//graph work. It deliberately does NOT recover each method's signature, so a
//resolved call still renders with rough, sometimes over-counted arguments until
//you type the callee — ordinary per-function RE, left to the analyst. Getting
//this far is the whole point: it reduces opaque indirect dispatch back to the
//normal "now go type this function" problem.
//
//Local classes (klass_<name> defined in this program): read the slot from the
//chunk and record the resolved call at the CALLIND so the decompiler renders a
//direct, named call. External classes (klass_<name> is an import, e.g.
//StringObject in libminiobj_rt.so): read the slot from the companion program
//(its chunk must have been typed by running Module 3 on it too — "runs on both"),
//register an external function, and route the resolved call through a ram-space
//thunk (a reference into the EXTERNAL space is silently ignored — the same
//reason Ghidra's loader builds ram-space PLT stubs for imports).
//
//The crux — and the exercise — is the reference you record at each CALLIND
//(see writeResolvedCall). Ghidra's reference model is typed far more finely than
//the code/data split tools like IDA expose — browse RefType and you'll find many
//call and flow kinds. The type you choose here is what decides whether the
//decompiler rewrites the indirect call into a direct, named one. Finding the
//right one is the last challenge of the workshop.
//
//Depends on the metadata script (the class structs exist) and the
//allocation-typing script (object variables carry their class type).
//@category PCodeWorkshop

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.script.GhidraScript;
import ghidra.framework.model.DomainFile;
import ghidra.framework.model.DomainObject;
import ghidra.framework.model.Project;
import ghidra.program.model.address.Address;
import ghidra.program.model.address.AddressSet;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.Pointer;
import ghidra.program.model.data.Structure;
import ghidra.program.model.data.TypeDef;
import ghidra.program.model.listing.Data;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.GhidraClass;
import ghidra.program.model.listing.Program;
import ghidra.program.model.mem.MemoryBlock;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.symbol.ExternalLocation;
import ghidra.program.model.symbol.RefType;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.ReferenceManager;
import ghidra.program.model.symbol.Namespace;
import ghidra.program.model.symbol.SourceType;
import ghidra.program.model.symbol.Symbol;
import ghidra.program.model.symbol.SymbolIterator;
import ghidra.program.model.symbol.SymbolTable;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

public class Module5_DispatchResolution extends GhidraScript {

    /** Cache of external (libName, funcName) → internal thunk address. */
    private Map<String, Function> thunkCache = new HashMap<>();
    private static final long THUNK_BLOCK_BASE = 0x80000000L;
    private static final int  THUNK_BLOCK_SIZE = 0x200;
    private Address nextThunkAddr;

    /** Strip COPY/CAST/PTRSUB(x, 0) chains — these are address-cast noise. */
    private Varnode unwrap(Varnode v) {
        while (true) {
            PcodeOp def = v.getDef();
            if (def == null) return v;
            int op = def.getOpcode();
            if (op == PcodeOp.COPY || op == PcodeOp.CAST) v = def.getInput(0);
            else if (op == PcodeOp.PTRSUB && def.getInput(1).isConstant()
                    && def.getInput(1).getOffset() == 0) v = def.getInput(0);
            else return v;
        }
    }

    /**
     * EXERCISE — pull the method slot out of the typed dispatch.
     *
     * The decompiler has already done the hard part. With the receiver typed (Module
     * 3 for app classes; Module 4's generic {@code KlassChunk} fallback for external
     * ones), the dispatch LOAD(obj->_klass) → LOAD(klass->methods[slot]) → CALLIND
     * decompiles as a typed array access: {@code PTRADD(&klass->methods, slot, 8)}.
     * So from the CALLIND target, find the inner LOAD, require a {@code PTRADD} with
     * 8-byte (pointer) elements, and read the slot straight off its index — no offset
     * math. Return null for anything else: a raw {@code INT_ADD} or non-8 element
     * size means the object wasn't typed, and this module only resolves typed
     * dispatches (typing the receiver is the prerequisite the earlier modules set up).
     */
    private Integer extractSlot(Varnode callIndTarget) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        PcodeOp loadOp = unwrap(callIndTarget).getDef();
        if (loadOp == null || loadOp.getOpcode() != PcodeOp.LOAD) return null;
        PcodeOp addrOp = unwrap(loadOp.getInput(1)).getDef();
        if (addrOp == null || addrOp.getOpcode() != PcodeOp.PTRADD) return null;
        if (addrOp.getInput(2).getOffset() != 8) return null; // not a pointer-array index
        return (int) addrOp.getInput(1).getOffset();
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * EXERCISE — read the receiver's recovered TYPE to identify its class.
     *
     * This is the workshop's payoff: Module 3 typed the receiver, Module 4 typed
     * the allocations, and the method target is a function of that type. {@link #unwrap}
     * the Varnode, take its {@link HighVariable#getDataType()}, peel any pointer and
     * typedef layers off, and if the base is a {@link Structure} return it (the
     * class struct); otherwise null (the object wasn't typed — nothing to resolve).
     */
    private Structure classFromVarnodeType(Varnode obj) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        obj = unwrap(obj);
        HighVariable hv = obj.getHigh();
        if (hv == null) return null;
        DataType dt = hv.getDataType();
        while (dt instanceof Pointer p) dt = p.getDataType();
        while (dt instanceof TypeDef td) dt = td.getBaseDataType();
        return (dt instanceof Structure s) ? s : null;
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /** The receiver argument's recovered type. In high P-code a CALLIND's input 0 is
     *  the indirect target and input 1 is the first real argument — `self` for every
     *  MiniObj method call. Returns null when that receiver isn't typed: this module
     *  deliberately resolves ONLY dispatches whose receiver already carries a class
     *  type. Getting it typed is the prerequisite the earlier modules establish. */
    private Structure dispatchClass(PcodeOpAST callOp) {
        if (callOp.getNumInputs() <= 1) return null;
        return classFromVarnodeType(callOp.getInput(1));
    }

    /**
     * Bridge from the class TYPE to its metadata anchor in memory: the
     * `klass_<name>` global {@link Symbol} (a labeled {@link Address}). The runtime
     * names one such global per class, so the {@link Structure}'s name maps straight
     * to it. Returns null when the class is external — its `klass_<name>` is an
     * unreadable import with no defining symbol here, so the caller falls back to
     * the companion program.
     */
    private Symbol klassSymbol(Structure cls) {
        return firstMemorySymbol(currentProgram, "klass_" + cls.getName());
    }

    /**
     * EXERCISE — read the method {@link Function} from the class's metadata chunk,
     * using the structure Module 3 already applied — no hand-computed offsets.
     *
     * The slot→method mapping lives in the METADATA, not in any namespace (a
     * {@link GhidraClass} groups methods by name, but has no slot ordering). The
     * {@code klass_<name>} {@link Symbol}'s data is a typed pointer to the chunk:
     * {@link #getDataAt} it and take its value for the chunk address. The chunk is
     * the {@code KlassChunk_<name>} struct Module 3 applied, so navigate it by field
     * ({@link #componentByName}) instead of byte math — take its {@code methods[]}
     * array field, whose {@code slot}-th entry holds the method pointer. Return the
     * {@link Function} there, or null if the slot is empty / no function exists.
     */
    private Function localMethod(Symbol klassSym, int slot) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        Data klassPtr = getDataAt(klassSym.getAddress());
        if (klassPtr == null || !(klassPtr.getValue() instanceof Address chunkAddr)) return null;
        Data chunk = getDataAt(chunkAddr);
        if (chunk == null) return null;
        Data methods = componentByName(chunk, "methods");
        if (methods == null || slot < 0 || slot >= methods.getNumComponents()) return null;
        Object fn = methods.getComponent(slot).getValue();
        return (fn instanceof Address fnAddr) ? getFunctionAt(fnAddr) : null;
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /** The sub-component of a struct {@link Data} with the given field name (or
     *  null) — {@link Data} indexes only by ordinal, so this reads a field
     *  by its name from Module 3's applied struct. */
    private Data componentByName(Data struct, String fieldName) {
        for (int i = 0; i < struct.getNumComponents(); i++) {
            Data c = struct.getComponent(i);
            if (fieldName.equals(c.getFieldName())) return c;
        }
        return null;
    }

    private record ExternalMethod(String libName, String methodName, long methodOffset) {}

    /** A class whose `klass_<name>` is an import: find the companion program
     *  that defines it, read the chunk slot there, and return (lib, method,
     *  offset-in-companion). */
    private ExternalMethod resolveExternalSlot(String className, int slot) throws Exception {
        String klassName = "klass_" + className;
        Project project = state.getProject();
        if (project == null) return null;

        for (DomainFile file : project.getProjectData().getRootFolder().getFiles()) {
            if (file.getName().equals(currentProgram.getName())) continue;
            DomainObject obj = file.getDomainObject(this, false, false, monitor);
            try {
                if (!(obj instanceof Program companion)) continue;
                if (!companion.getLanguageID().equals(currentProgram.getLanguageID())) continue;
                Symbol klassPtr = firstMemorySymbol(companion, klassName);
                if (klassPtr == null) continue;
                try {
                    /* `klass_X` is a pointer variable: read its value for the chunk. */
                    long chunkOff = companion.getMemory().getLong(klassPtr.getAddress());
                    if (chunkOff == 0L) continue;
                    Address chunkAddr = companion.getAddressFactory()
                        .getDefaultAddressSpace().getAddress(chunkOff);
                    /* The chunk is a KlassChunk struct IF Module 3 was also run on the
                     * companion — so navigate it by field, exactly like localMethod,
                     * instead of hand-computing the slot offset. (If the companion
                     * wasn't run through Module 3 the chunk is untyped: getDataAt
                     * returns null and it is skipped — external resolution then needs
                     * that metadata pass first.) */
                    Data chunk = companion.getListing().getDataAt(chunkAddr);
                    if (chunk == null) continue;
                    Data methods = componentByName(chunk, "methods");
                    if (methods == null || slot < 0 || slot >= methods.getNumComponents()) continue;
                    if (!(methods.getComponent(slot).getValue() instanceof Address fnAddr)) continue;
                    Function fn = companion.getFunctionManager().getFunctionAt(fnAddr);
                    String fnName = (fn != null && !fn.getName().startsWith("FUN_"))
                        ? fn.getName()
                        : className + "_slot" + slot;
                    return new ExternalMethod(file.getName(), fnName, fnAddr.getOffset());
                } catch (Exception readErr) {
                    /* this companion has the symbol but unreadable/untyped data — skip */
                    continue;
                }
            } finally {
                obj.release(this);
            }
        }
        return null;
    }

    /** Find or create the {@link GhidraClass} namespace for a class struct — by
     *  name, the same struct↔class correlation Module 3 relies on. */
    private GhidraClass classNamespace(Structure struct) throws Exception {
        SymbolTable symTab = currentProgram.getSymbolTable();
        Namespace global = currentProgram.getGlobalNamespace();
        Namespace ns = symTab.getNamespace(struct.getName(), global);
        if (ns instanceof GhidraClass gc) return gc;
        if (ns == null) return symTab.createClass(global, struct.getName(), SourceType.ANALYSIS);
        return symTab.convertNamespaceToClass(ns);
    }

    /**
     * Get (or create) the local {@link Function} that stands in for an external
     * method's slot. You can't point a reference directly at a method that lives in
     * another program, so this is two conceptual steps, cached per (class, slot):
     *
     * <ol>
     *   <li>{@link #createLocalThunk} — a LOCAL stub named {@code method_<slot>} in
     *       the receiver's {@link GhidraClass}. This is everything you know without
     *       leaving the program: it gives the dispatch a local target, so the
     *       reference resolves and xrefs/the call graph work — even before you know
     *       which external method it actually is.</li>
     *   <li>{@link #linkThunkToExternal} — only now go look the slot up in the
     *       companion program, mark the stub as a thunk to that import, and promote
     *       the external method name to the stub's PRIMARY symbol (so the call reads
     *       {@code Class::<method>}). {@code method_<slot>} is kept as a SECONDARY
     *       label — the slot index is how you re-find this stub for the next call
     *       site. Skipped (stub stays {@code method_<slot>}) if the companion is
     *       absent.</li>
     * </ol>
     */
    private Function getOrCreateThunk(GhidraClass cls, int slot) throws Exception {
        String key = cls.getName() + "::method_" + slot;
        Function cached = thunkCache.get(key);
        if (cached != null) return cached;

        Function existing = findExistingThunk(cls, slot);
        if (existing != null) {
            thunkCache.put(key, existing);
            return existing;
        }

        Function thunk = createLocalThunk(cls, slot);              // step 1: local stub
        if (thunk != null) linkThunkToExternal(thunk, cls.getName(), slot);  // step 2: external assoc
        thunkCache.put(key, thunk);
        return thunk;
    }

    /**
     * STEP 1 — materialize a LOCAL stub for the slot, with only local knowledge.
     *
     * A {@link RefType#CALL_OVERRIDE_UNCONDITIONAL} reference (see
     * {@link #writeResolvedCall}) must point at an address in THIS program; a
     * reference into another program's EXTERNAL space is silently dropped — the
     * same reason Ghidra's loader synthesizes ram-space PLT stubs for imports. So
     * declare a {@link Function} at the next free address in a synthetic block,
     * named {@code method_<slot>} and filed under the receiver's {@link GhidraClass}.
     * Like Ghidra's own import stubs, the stub needs no instruction bytes — the
     * block is uninitialized and the function is created over a single-address body
     * straight through the {@code FunctionManager}. That alone makes the dispatch
     * resolve to a real local target — no external information needed yet.
     */
    private Function createLocalThunk(GhidraClass cls, int slot) throws Exception {
        if (nextThunkAddr == null) {
            Address base = currentProgram.getAddressFactory()
                .getDefaultAddressSpace().getAddress(THUNK_BLOCK_BASE);
            MemoryBlock block = currentProgram.getMemory().getBlock("synthetic_thunks");
            if (block == null) {
                block = currentProgram.getMemory().createUninitializedBlock(
                    "synthetic_thunks", base, THUNK_BLOCK_SIZE, false);
                block.setRead(true); block.setExecute(true);
            }
            nextThunkAddr = base;
        }
        while (currentProgram.getFunctionManager().getFunctionAt(nextThunkAddr) != null) {
            nextThunkAddr = nextThunkAddr.add(8);
        }
        Address thunkAddr = nextThunkAddr;
        nextThunkAddr = nextThunkAddr.add(8);

        Function thunk = currentProgram.getFunctionManager().getFunctionAt(thunkAddr);
        if (thunk == null) {
            thunk = currentProgram.getFunctionManager().createFunction(
                "method_" + slot, cls, thunkAddr, new AddressSet(thunkAddr, thunkAddr),
                SourceType.ANALYSIS);
        }
        return thunk;
    }

    /**
     * STEP 2 — associate the local stub with the real external symbol.
     *
     * Only now go find what the slot actually is: resolve the method in the
     * companion program ({@link #resolveExternalSlot}), register it as an external
     * function, and mark the stub as a thunk to it — connecting the call graph to
     * the real import — then promote the external name to the primary symbol while
     * preserving {@code method_<slot>} as a secondary label (see below). Returns
     * false (no link) when the companion program isn't loaded — the local stub
     * still works on its own.
     */
    private boolean linkThunkToExternal(Function thunk, String className, int slot)
            throws Exception {
        ExternalMethod em = resolveExternalSlot(className, slot);
        if (em == null) return false;
        Address extAddr = currentProgram.getAddressFactory()
            .getDefaultAddressSpace().getAddress(em.methodOffset);
        ExternalLocation extLoc = currentProgram.getExternalManager()
            .addExtFunction(em.libName, em.methodName, extAddr, SourceType.ANALYSIS);
        thunk.setThunkedFunction(extLoc.getFunction());
        /* Promote the external method's name to the PRIMARY symbol so the call
         * renders as Class::<method>. But keep method_<slot> as a SECONDARY label at
         * the same address: the slot index is what lets findExistingThunk re-locate
         * this stub when another call site hits the same (class, slot), and a bare
         * external name alone would drop it. Order matters — rename first, so the
         * label no longer collides with the (now former) primary name. */
        Namespace ns = thunk.getParentNamespace();
        thunk.setName(em.methodName, SourceType.ANALYSIS);
        currentProgram.getSymbolTable()
            .createLabel(thunk.getEntryPoint(), "method_" + slot, ns, SourceType.ANALYSIS);
        return true;
    }

    /** Re-run idempotency: find a stub already created for this (class, slot).
     *  Matches the {@code method_<slot>} label in the class namespace — the primary
     *  symbol once the companion is absent, a secondary label once the stub has been
     *  linked and renamed to the external method. Checking ALL symbols at the address
     *  (not just the function's primary name) is what makes the secondary label
     *  findable after linking. */
    private Function findExistingThunk(GhidraClass cls, int slot) {
        MemoryBlock block = currentProgram.getMemory().getBlock("synthetic_thunks");
        if (block == null) return null;
        SymbolTable symTab = currentProgram.getSymbolTable();
        Address cur = block.getStart();
        Address end = block.getEnd();
        while (cur.compareTo(end) <= 0) {
            for (Symbol s : symTab.getSymbols(cur)) {
                if (s.getName().equals("method_" + slot)
                        && s.getParentNamespace() != null
                        && s.getParentNamespace().getName().equals(cls.getName())) {
                    return currentProgram.getFunctionManager().getFunctionAt(cur);
                }
            }
            cur = cur.add(8);
        }
        return null;
    }

    private Symbol firstMemorySymbol(Program p, String name) {
        SymbolIterator it = p.getSymbolTable().getSymbols(name);
        while (it.hasNext()) {
            Symbol s = it.next();
            if (s.isExternal()) continue;
            Address a = s.getAddress();
            if (!a.isMemoryAddress()) continue;
            /* Skip EXTERNAL-block (and any uninitialized) stubs. Ghidra's
             * EXTERNAL block lives in ram space, so its klass_X labels report
             * isExternal()==false and isMemoryAddress()==true yet hold no
             * readable bytes — reading one throws MemoryAccessException. Only a
             * program that *defines* the class (the runtime .so) has klass_X in
             * initialized .data.rel.ro. Requiring an initialized block both
             * fixes the crash and makes localMethod correctly treat imported
             * classes as external. */
            MemoryBlock b = p.getMemory().getBlock(a);
            if (b == null || !b.isInitialized()) continue;
            return s;
        }
        return null;
    }

    /**
     * EXERCISE — record the resolved call at the CALLIND so the decompiler emits a
     * direct, named call to {@code target} instead of {@code (**(code **)(...))()}.
     *
     * This is the capstone decision. Ghidra distinguishes far more reference kinds
     * than the code/data split other tools expose — browse {@link RefType} — and
     * the kind you record here is what decides whether the decompiler rewrites the
     * indirect call. Add a primary reference of the right type from {@code callInd}
     * to {@code target}.
     */
    private void writeResolvedCall(ReferenceManager refMgr, Address callInd, Address target) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        // A CALL_OVERRIDE_UNCONDITIONAL turns the CALLIND into a direct CALL to
        // `target` in the DECOMPILER. A plain call reference (e.g. COMPUTED_CALL)
        // updates the listing's xrefs and the call graph, but the decompiler keeps
        // rendering the opaque indirect call — only an override-type call reference
        // reaches the decompiler, and only when it is primary and the unique one.
        Reference ref = refMgr.addMemoryReference(callInd, target,
            RefType.CALL_OVERRIDE_UNCONDITIONAL, SourceType.ANALYSIS, 0);
        refMgr.setPrimary(ref, true);
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    @Override
    public void run() throws Exception {
        var decomp = new DecompInterface();
        /* === CRITICAL: push Java's default DecompileOptions so readonlypropagate
         * is on and the object's typed variable is recovered (see the
         * allocation-typing script). */
        decomp.setOptions(new DecompileOptions());
        decomp.openProgram(currentProgram);

        int tx = currentProgram.startTransaction("resolve dispatch CALLINDs (type-driven)");
        boolean ok = false;
        int local = 0, external = 0, untyped = 0;
        try {
            var fm = currentProgram.getFunctionManager();
            var refMgr = currentProgram.getReferenceManager();
            for (Function caller : fm.getFunctions(true)) {
                if (caller.isThunk() || caller.isExternal()) continue;
                HighFunction hf = decomp.decompileFunction(caller, 30, monitor).getHighFunction();
                if (hf == null) continue;
                Iterator<PcodeOpAST> ops = hf.getPcodeOps();
                while (ops.hasNext()) {
                    PcodeOpAST op = ops.next();
                    if (op.getOpcode() != PcodeOp.CALLIND) continue;
                    Integer slot = extractSlot(op.getInput(0));
                    if (slot == null) continue;
                    Address callInd = op.getSeqnum().getTarget();

                    Structure struct = dispatchClass(op);
                    if (struct == null) {
                        /* Receiver not typed at the call site — out of scope: this
                         * module only resolves dispatches whose receiver is typed. */
                        untyped++;
                        continue;
                    }

                    Symbol klassSym = klassSymbol(struct);   // Structure -> Symbol (null if external)
                    Function target = (klassSym != null) ? localMethod(klassSym, slot) : null;
                    if (target != null) {
                        writeResolvedCall(refMgr, callInd, target.getEntryPoint());
                        println("  " + callInd + " → " + struct.getName() + " slot " + slot
                            + " @ " + target.getEntryPoint());
                        local++;
                        continue;
                    }

                    /* External class: create a LOCAL stub now (so the dispatch has a
                     * real local target and xrefs work), then associate it with the
                     * external symbol — which renames it from method_<slot> to the
                     * real method name. The stub is created and the call resolved
                     * regardless of whether the companion is loaded. */
                    GhidraClass cls = classNamespace(struct);
                    Function thunk = getOrCreateThunk(cls, slot);
                    if (thunk == null) {
                        println("  " + callInd + " → " + struct.getName() + " slot " + slot
                            + " (external, stub creation failed)");
                        external++;
                        continue;
                    }
                    writeResolvedCall(refMgr, callInd, thunk.getEntryPoint());
                    boolean linked = thunk.getThunkedFunction(false) != null;
                    println("  " + callInd + " → " + thunk.getName(true)
                        + " via thunk @ " + thunk.getEntryPoint() + " (external slot " + slot + ")"
                        + (linked ? "" : " (companion unavailable)"));
                    external++;
                }
            }
            ok = true;
        } finally {
            decomp.dispose();
            currentProgram.endTransaction(tx, ok);
        }
        println("Resolved " + local + " local + " + external + " external dispatch site(s)"
            + (untyped > 0 ? ", " + untyped + " untyped (object class unknown)" : ""));
    }
}
