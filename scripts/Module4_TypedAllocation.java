//@category PCodeWorkshop

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.decompiler.util.FillOutStructureHelper;
import ghidra.app.script.GhidraScript;
import ghidra.program.database.SpecExtension;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.ArrayDataType;
import ghidra.program.model.data.CategoryPath;
import ghidra.program.model.data.DataType;
import ghidra.program.model.data.DataTypeConflictHandler;
import ghidra.program.model.data.FunctionDefinitionDataType;
import ghidra.program.model.data.ParameterDefinition;
import ghidra.program.model.data.ParameterDefinitionImpl;
import ghidra.program.model.data.PointerDataType;
import ghidra.program.model.data.Structure;
import ghidra.program.model.data.StructureDataType;
import ghidra.program.model.data.UnsignedLongDataType;
import ghidra.program.model.listing.Function;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.HighFunctionDBUtil;
import ghidra.program.model.pcode.HighVariable;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.Symbol;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Module 4 — Provide & propagate type information.
 *
 * Module 3 typed one thing per method: the receiver, via {@code __thiscall}. Most
 * objects in a function are NOT the receiver — they're freshly allocated, or
 * reached through a field — and stay opaque ({@code (**(code **)(*x + 0x28))(...)}).
 * This module makes those legible by getting a class type onto them and letting
 * the decompiler propagate it, so dispatches read {@code obj->_klass->methods[N]}:
 * the target isn't resolved yet, but the class of {@code obj} and the slot
 * {@code N} are now plain.
 *
 * It is ONE linear story told in three beats, each beat's payoff feeding the next:
 *
 *   BEAT 1 — RESTORE.  Every allocation is {@code OBJ_NEW(T) == rt_retain(rt_alloc(klass_T))},
 *     and the runtime laces object handoffs with {@code rt_retain}/{@code rt_release}/
 *     {@code rt_store_strong}. To the decompiler those are opaque calls that SWALLOW
 *     the dataflow — a type put on the {@code rt_alloc} result dies at the {@code rt_retain}
 *     wrapper and never reaches the use site (try beat 2 first and watch it fail).
 *     Beat 1 installs compiler-spec call-fixups that inline them ({@code rt_retain} → identity,
 *     etc.). Payoff: the GC noise is gone and the alloc→use dataflow is whole again.
 *     This swallow-the-dataflow problem is common in real targets (refcounting, accessor shims).
 *
 *   BEAT 2 — INJECT.  With dataflow restored, beat 2 makes each {@code rt_alloc} call a
 *     TYPE SOURCE: resolve its {@code klass} argument to a class, then attach a
 *     per-call-site return-type override ({@link HighFunctionDBUtil#writeOverride}).
 *     The decompiler propagates that type through the function on its own — every
 *     use of the allocated object becomes typed, and dispatches on it go structural.
 *
 *   BEAT 3 — PROPAGATE.  Injection stops at the function boundary: a {@code Config}'s
 *     {@code owner} is set in the constructor but read in the collectors, so it stays
 *     opaque there. Beat 3 runs Ghidra's fill-struct ({@link FillOutStructureHelper}) over
 *     the now-typed allocations; it harvests field types from the typed stores
 *     ({@code config->owner = this}, with {@code this : Monitor *}) and writes them
 *     onto the struct — basic inter-procedural propagation. Payoff: owner-reached
 *     dispatches go structural too.
 *
 * Scope: the 15 app classes (with {@code KlassChunk} types from Module 3) reach
 * {@code obj->_klass->methods[N]}; runtime/external classes (File, Codec, …) render
 * {@code obj->_klass + offset} — their chunk lives in the {@code .so}; that's Module 5.
 *
 * Depends on Module 3 (class structs + namespaces) having run first.
 */
public class Module4_TypedAllocation extends GhidraScript {

    @Override
    public void run() throws Exception {
        // ======================= BEAT 1 — RESTORE =======================
        // Inline the GC wrappers so a type can survive crossing OBJ_NEW. Do this
        // BEFORE opening the decompiler: installing the call-fixups changes the
        // compiler spec, and a DecompInterface caches the spec at openProgram time.
        int attached = installCallFixups();
        println("BEAT 1 (restore): installed " + fixupsForCurrentProgram().size()
            + " GC call-fixups, attached to " + attached + " function(s)."
            + " rt_retain/rt_release/rt_store_strong are now see-through.");

        DecompInterface decomp = new DecompInterface();
        /* === CRITICAL: push Java's default DecompileOptions to the C++ decompiler.
         * Without this, `readonlypropagate` stays false and the decompiler refuses
         * to fold GOT/.rodata loads into constants — every rt_alloc(klass_X) site
         * shows `*(undefined8 *)PTR_klass_X` instead of a resolvable constant. The
         * Ghidra UI sets this for you; standalone scripts must do it explicitly. */
        decomp.setOptions(new DecompileOptions());
        decomp.openProgram(currentProgram);
        try {
            // ======================= BEAT 2 — INJECT ========================
            // Make each rt_alloc call a type source.
            List<AllocSite> sites = collectAllocSites(decomp);
            println("\nBEAT 2 (inject): " + sites.size() + " rt_alloc call site(s) resolved.");

            int txId = currentProgram.startTransaction("Module4: inject rt_alloc return types");
            boolean ok = false;
            try {
                int applied = 0;
                for (AllocSite s : sites) {
                    DataType ptr = new PointerDataType(
                        getOrCreateClassStruct(s.className(), (int) s.instanceSize()));
                    try {
                        applyReturnOverride(s.caller(), s.callAddr(), s.className(), ptr);
                        applied++;
                    } catch (Exception ex) {
                        printerr("  WARN: override at " + s.callAddr() + " failed: " + ex.getMessage());
                    }
                }
                ok = true;
                println("  applied " + applied + " return-type override(s) across "
                    + countClasses(sites) + " class(es).");
            } finally {
                currentProgram.endTransaction(txId, ok);
            }

            // ======================= BEAT 3 — PROPAGATE =====================
            // Push types across the call boundary via fill-struct.
            int fields = propagateFields(sites, decomp);
            println("\nBEAT 3 (propagate): fill-struct typed " + fields
                + " field(s) on existing class structs (e.g. Config::owner = Monitor *).");

            reportStringObjectSites(sites);
        } finally {
            decomp.dispose();
        }
    }

    /**
     * BEAT 2 EXERCISE — make one {@code rt_alloc} call site a type source.
     *
     * {@code rt_alloc} returns {@code void *} globally, but at THIS site you know the
     * concrete class. Build a {@link FunctionDefinitionDataType} whose return type is
     * {@code returnType} (a {@code <Class> *}) and one {@code klass} pointer argument,
     * then attach it to the call at {@code callAddr} with
     * {@link HighFunctionDBUtil#writeOverride(Function, Address, ghidra.program.model.data.FunctionSignature)}.
     * That makes the decompiler treat this call's result as {@code returnType} and
     * propagate it through the function — no need to touch any of the uses.
     */
    private void applyReturnOverride(Function caller, Address callAddr, String className,
            DataType returnType) throws Exception {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        var sig = new FunctionDefinitionDataType(
            "rt_alloc_returning_" + className, currentProgram.getDataTypeManager());
        sig.setReturnType(returnType);
        sig.setArguments(new ParameterDefinition[] {
            new ParameterDefinitionImpl("klass", new PointerDataType(), null)
        });
        HighFunctionDBUtil.writeOverride(caller, callAddr, sig);
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * BEAT 2 EXERCISE — trace a call argument back to the constant address it carries.
     *
     * Before {@link #applyReturnOverride} can type a site, {@link #collectAllocSites}
     * has to learn WHICH class each {@code rt_alloc} allocates — and that means
     * following its first argument (the {@code klass}) back to the metadata address it
     * points at. It is rarely a constant at the CALL: BEAT 1 healed the dataflow and
     * {@code readonlypropagate} already folded the GOT/.rodata load into a constant,
     * but the value still reaches the call through cast/copy noise and a
     * {@code PTRSUB} — Ghidra's "base + constant offset", how it addresses a global.
     * This is the same backward def-use walk as Module 2's {@code traceToAddress},
     * with one extra op to step through.
     *
     * Walk {@link Varnode#getDef()} backwards (the P-Code is SSA — one def per Varnode):
     * <ul>
     *   <li>a non-zero constant → {@link #toAddr}; an address Varnode → its address;</li>
     *   <li>{@code COPY}/{@code CAST} → recurse on input 0 (value-preserving);</li>
     *   <li>{@code PTRSUB(base, off)} → the address is base+off; input 0 usually
     *       carries it, so try input 0, then fall back to input 1;</li>
     *   <li>anything else, or no def → null.</li>
     * </ul>
     * Bound the recursion with {@code depth} (give up past ~10) so an unexpected graph
     * can't loop forever. Returning null is fine: the caller reads it as "klass came
     * from a parameter" and skips the site (that case is deferred to Module 5).
     */
    private Address resolveToAddress(Varnode v, int depth) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        if (depth > 10) return null;
        if (v.isConstant() && v.getOffset() != 0L) return toAddr(v.getOffset());
        if (v.isAddress()) return v.getAddress();
        PcodeOp def = v.getDef();
        if (def == null) return null;
        switch (def.getOpcode()) {
            case PcodeOp.COPY:
            case PcodeOp.CAST:
                return resolveToAddress(def.getInput(0), depth + 1);
            case PcodeOp.PTRSUB: {
                Address fromBase = resolveToAddress(def.getInput(0), depth + 1);
                return (fromBase != null) ? fromBase : resolveToAddress(def.getInput(1), depth + 1);
            }
            default:
                return null;
        }
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    // ============================ PROVIDED — BEAT 1 ============================

    /**
     * Install the GC call-fixups (compiler-spec extension) and attach each to its
     * matching function(s). Returns the number of (function, fixup) attachments.
     *
     * This attaches by hand rather than re-running Ghidra's {@code CallFixupAnalyzer}.
     * That analyzer is what normally attaches compiler-spec fixups during initial
     * auto-analysis, but it caches its target→fixup map in static fields keyed on
     * (languageID, compilerSpecID). Re-invoking it after
     * {@code addReplaceCompilerSpecExtension} returns the stale cached map, so the
     * fixups just added are never seen. A short walk over getFunctions() does
     * exactly what the analyzer would, without the cache.
     */
    private int installCallFixups() throws Exception {
        int attached = 0;
        int tx = currentProgram.startTransaction("Module4: install GC call fixups");
        boolean ok = false;
        try {
            var specExt = new SpecExtension(currentProgram);
            for (var e : fixupsForCurrentProgram().entrySet()) {
                specExt.addReplaceCompilerSpecExtension(e.getValue(), monitor);
                for (Function f : currentProgram.getFunctionManager().getFunctions(true)) {
                    if (e.getKey().equals(f.getName())) {
                        f.setCallFixup(e.getKey());
                        attached++;
                    }
                }
            }
            ok = true;
        } finally {
            currentProgram.endTransaction(tx, ok);
        }
        return attached;
    }

    /** Sleigh P-Code fixups for the current architecture's C ABI: rt_retain is the
     *  identity on the first arg, rt_release is a no-op, rt_store_strong is a store. */
    private Map<String, String> fixupsForCurrentProgram() {
        String proc = currentProgram.getLanguage().getProcessor().toString().toLowerCase();
        String arg0 = proc.contains("aarch64") ? "x0" : "RDI";
        String arg1 = proc.contains("aarch64") ? "x1" : "RSI";
        String ret  = proc.contains("aarch64") ? "x0" : "RAX";
        var fixups = new LinkedHashMap<String, String>();
        fixups.put("rt_retain", callfixup("rt_retain", ret + " = " + arg0 + ";"));
        fixups.put("rt_release", callfixup("rt_release", "temp:1 = 0;"));
        fixups.put("rt_store_strong", callfixup("rt_store_strong", "*:8 " + arg0 + " = " + arg1 + ";"));
        return fixups;
    }

    private static String callfixup(String name, String body) {
        return "<callfixup name=\"" + name + "\">\n"
             + "  <target name=\"" + name + "\"/>\n"
             + "  <pcode><body><![CDATA[\n" + body + "\n]]></body></pcode>\n"
             + "</callfixup>";
    }

    // ============================ PROVIDED — BEAT 2 ============================

    private record AllocSite(Address callAddr, Function caller, String className, long instanceSize) {}

    /** Find every rt_alloc call site and resolve its klass argument to a class. */
    private List<AllocSite> collectAllocSites(DecompInterface decomp) throws Exception {
        List<Function> rtAllocFuncs = findFuncsNamed("rt_alloc");
        var rtAllocEntries = new java.util.HashSet<Address>();
        for (Function f : rtAllocFuncs) rtAllocEntries.add(f.getEntryPoint());

        var callers = new LinkedHashMap<Address, Function>();
        for (Function target : rtAllocFuncs) {
            for (Reference ref : getReferencesTo(target.getEntryPoint())) {
                if (!ref.getReferenceType().isCall()) continue;
                Function caller = getFunctionContaining(ref.getFromAddress());
                if (caller == null || caller.isThunk()) continue;
                if (rtAllocEntries.contains(caller.getEntryPoint())) continue;
                callers.putIfAbsent(caller.getEntryPoint(), caller);
            }
        }

        var sites = new ArrayList<AllocSite>();
        for (Function caller : callers.values()) {
            HighFunction hf = decomp.decompileFunction(caller, 30, monitor).getHighFunction();
            if (hf == null) continue;
            Iterator<PcodeOpAST> ops = hf.getPcodeOps();
            while (ops.hasNext()) {
                PcodeOpAST op = ops.next();
                if (op.getOpcode() != PcodeOp.CALL) continue;
                if (!rtAllocEntries.contains(op.getInput(0).getAddress())) continue;
                if (op.getNumInputs() < 2) continue;
                Address callAddr = op.getSeqnum().getTarget();
                Address chunkArg = resolveToAddress(op.getInput(1), 0);
                if (chunkArg == null) continue; // klass came from a param — defer to Module 5

                Address realChunk = pickChunk(chunkArg);
                String className = null;
                long instanceSize = 0;
                if (realChunk != null) {
                    className = readCString(toAddr(getLong(realChunk)), 64);
                    instanceSize = getLong(realChunk.add(8));
                } else {
                    Symbol sym = currentProgram.getSymbolTable().getPrimarySymbol(chunkArg);
                    if (sym != null && sym.getName().startsWith("klass_")) {
                        className = sym.getName().substring("klass_".length());
                    }
                }
                if (!isValidClassName(className)) continue;
                sites.add(new AllocSite(callAddr, caller, className, instanceSize));
            }
        }
        return sites;
    }

    // ============================ PROVIDED — BEAT 3 ============================

    /** Run fill-struct over every typed allocation result. With createNewStructure
     *  false it EXTENDS the existing class struct (from Module 3), harvesting field
     *  types from the typed stores it sees — e.g. `config->owner = this` (Monitor *)
     *  in the constructor. Returns the number of components added across all structs. */
    private int propagateFields(List<AllocSite> sites, DecompInterface decomp) throws Exception {
        var byCaller = new LinkedHashMap<Address, Function>();
        for (AllocSite s : sites) byCaller.putIfAbsent(s.caller().getEntryPoint(), s.caller());

        var helper = new FillOutStructureHelper(currentProgram, monitor);
        int added = 0;
        int tx = currentProgram.startTransaction("Module4: propagate field types (fill-struct)");
        boolean ok = false;
        try {
            for (Function caller : byCaller.values()) {
                HighFunction hf = decomp.decompileFunction(caller, 30, monitor).getHighFunction();
                if (hf == null) continue;
                Iterator<PcodeOpAST> ops = hf.getPcodeOps();
                while (ops.hasNext()) {
                    PcodeOpAST op = ops.next();
                    if (op.getOpcode() != PcodeOp.CALL || op.getOutput() == null) continue;
                    HighVariable hv = op.getOutput().getHigh();
                    if (hv == null || hv.getDataType() == null) continue;
                    // Only extend the MiniObj class structs (pointer to a /MiniObj struct).
                    if (!(stripPointer(hv.getDataType()) instanceof Structure st)) continue;
                    if (st.getCategoryPath() == null
                        || !"/MiniObj".equals(st.getCategoryPath().getPath())) continue;
                    int before = st.getNumDefinedComponents();
                    try {
                        helper.processStructure(hv, caller, false, false, decomp);
                        added += Math.max(0, st.getNumDefinedComponents() - before);
                    } catch (Exception ignore) {
                        /* skip vars fill-struct can't handle */
                    }
                }
            }
            ok = true;
        } finally {
            currentProgram.endTransaction(tx, ok);
        }
        return added;
    }

    private DataType stripPointer(DataType dt) {
        return (dt instanceof ghidra.program.model.data.Pointer p) ? p.getDataType() : null;
    }

    // ============================ PROVIDED — shared ============================

    /** The rt_alloc arg is either the chunk itself or the address of the `klass_X`
     *  pointer variable holding it; try direct, then one dereference. null = import. */
    private Address pickChunk(Address a) {
        if (looksLikeChunk(a)) return a;
        try {
            Address deref = toAddr(getLong(a));
            if (looksLikeChunk(deref)) return deref;
        } catch (Exception ignored) { /* unreadable -> external import */ }
        return null;
    }

    private boolean looksLikeChunk(Address chunk) {
        try {
            long namePtr = getLong(chunk);
            return namePtr != 0 && isValidClassName(readCString(toAddr(namePtr), 64));
        } catch (Exception e) {
            return false;
        }
    }

    private String readCString(Address addr, int maxLen) {
        var sb = new StringBuilder();
        for (int i = 0; i < maxLen; i++) {
            byte b;
            try { b = currentProgram.getMemory().getByte(addr.add(i)); }
            catch (Exception e) { return null; }
            if (b == 0) return sb.toString();
            sb.append((char) (b & 0xFF));
        }
        return sb.toString();
    }

    /** Strict ASCII identifier — stricter than Character.isJavaIdentifier* so a
     *  misread chunk address can't masquerade as a class name. */
    private static boolean isValidClassName(String s) {
        if (s == null || s.isEmpty() || s.length() > 64) return false;
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            boolean ok = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') || c == '_'
                || (i > 0 && c >= '0' && c <= '9');
            if (!ok) return false;
        }
        return true;
    }

    private List<Function> findFuncsNamed(String name) {
        var out = new ArrayList<Function>();
        var fm = currentProgram.getFunctionManager();
        for (Function f : fm.getFunctions(true)) if (name.equals(f.getName())) out.add(f);
        for (Function f : fm.getExternalFunctions()) if (name.equals(f.getName())) out.add(f);
        return out;
    }

    /** Fetch (or create) the class struct. After Module 3 this returns the existing
     *  /MiniObj struct (with _klass typed as the class's specific KlassChunk pointer).
     *  For external classes M3 didn't see, create a placeholder whose _klass points at
     *  the GENERIC {@link #genericKlassChunk} — so a dispatch through it still
     *  decompiles as klass->methods[slot] (a typed array index), exactly like an app
     *  class, instead of raw `*(code **)(klass + offset)` byte arithmetic. */
    private DataType getOrCreateClassStruct(String className, int instanceSize) {
        var dtm = currentProgram.getDataTypeManager();
        var category = new CategoryPath("/MiniObj");
        DataType existing = dtm.getDataType(category, className);
        if (existing != null) return existing;
        int size = instanceSize > 0 ? instanceSize : 16;
        var struct = new StructureDataType(category, className, size);
        struct.replaceAtOffset(0, new PointerDataType(genericKlassChunk()), 8, "_klass", null);
        return dtm.addDataType(struct, DataTypeConflictHandler.REPLACE_HANDLER);
    }

    /** A generic klass-chunk layout (name, instance_size, method_count, methods[]) —
     *  the {@code _klass} pointee for classes with no specific {@code KlassChunk_<Name>}
     *  (the runtime's external classes). Same field shape as Module 3's per-class
     *  chunk, with methods[] sized generously so any dispatch slot indexes within it.
     *  That makes {@code klass->methods[slot]} a typed array access for external classes
     *  too — so the slot reads straight off the PTRADD index in Module 5. */
    private DataType genericKlassChunk() {
        var dtm = currentProgram.getDataTypeManager();
        var cat = new CategoryPath("/MiniObj");
        DataType existing = dtm.getDataType(cat, "KlassChunk");
        if (existing != null) return existing;
        var s = new StructureDataType(cat, "KlassChunk", 0);
        s.add(new PointerDataType(), 8, "name", null);
        s.add(new UnsignedLongDataType(), 8, "instance_size", null);
        s.add(new UnsignedLongDataType(), 8, "method_count", null);
        s.add(new ArrayDataType(new PointerDataType(), 64, 8), 8 * 64, "methods", null);
        return dtm.addDataType(s, DataTypeConflictHandler.REPLACE_HANDLER);
    }

    private int countClasses(List<AllocSite> sites) {
        var set = new java.util.HashSet<String>();
        for (AllocSite s : sites) set.add(s.className());
        return set.size();
    }

    private void reportStringObjectSites(List<AllocSite> sites) {
        var stringSites = new ArrayList<AllocSite>();
        for (AllocSite s : sites) if ("StringObject".equals(s.className())) stringSites.add(s);
        if (stringSites.isEmpty()) {
            println("\nNo StringObject allocations detected.");
            return;
        }
        println("\nStringObject allocation sites (gateway to the string-recovery module):");
        for (AllocSite s : stringSites) println("  " + s.callAddr() + " in " + s.caller().getName(true));
    }
}
