//@category PCodeWorkshop

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.decompiler.DecompilerLocation;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.data.CharDataType;
import ghidra.program.model.data.IntegerDataType;
import ghidra.program.model.data.PointerDataType;
import ghidra.program.model.data.VoidDataType;
import ghidra.program.model.listing.Data;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.Function.FunctionUpdateType;
import ghidra.program.model.listing.ParameterImpl;
import ghidra.program.model.listing.ReturnParameterImpl;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;
import ghidra.program.model.symbol.Reference;
import ghidra.program.model.symbol.SourceType;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;

/**
 * Module 2 — Recover function names from {@code rt_log} calls.
 *
 * In Module 1 the constant you wanted was folded right onto the op, so you could
 * read it off any op's input. This module adds the two ideas that the rest of
 * the workshop leans on:
 *
 *   1. FILTER FIRST. Not every op matters anymore — only the calls to one
 *      function, {@code rt_log}. So before doing any real work, narrow the
 *      P-Code down to just those callsites (and, in batch, only decompile the
 *      functions that call rt_log at all — the cross-references tell you which).
 *
 *   2. DATAFLOW (def-use). The interesting argument is not a constant sitting at
 *      the CALL. It is a Varnode that some earlier op produced — here a COPY of a
 *      pointer into {@code .rodata}. To get the value, follow {@link Varnode#getDef()}
 *      backwards, hop by hop, until you reach the constant/address it carries.
 *
 * Every {@code rt_log} call passes {@code __func__} as its second argument, i.e.
 * the enclosing function's own name (a {@code Class_method} string such as
 * {@code "DiskIoConfig_collect"}). Recovering it un-strips the function.
 */
public class Module2_RecoverNames extends GhidraScript {

    // false: scan the whole program (the demo / batch run).
    // true:  recover only for the function under the decompiler cursor.
    private static final boolean INTERACTIVE = false;

    // CALL inputs are [target, arg0, arg1, ...]; for rt_log(level, func, fmt, ...)
    // the func argument (== __func__) is therefore input index 2.
    private static final int RT_LOG_FUNC_ARG = 2;

    private int renamedCount = 0;

    @Override
    public void run() throws Exception {
        Function rtLog = findRtLog();
        if (rtLog == null) {
            printerr("Could not identify rt_log.");
            return;
        }
        println("Identified rt_log at " + rtLog.getEntryPoint() + " (" + rtLog.getName() + ")");

        int txId = currentProgram.startTransaction("Module2: recover names via rt_log");
        try {
            pinRtLogSignature(rtLog); // provided: tells the decompiler rt_log's shape

            if (INTERACTIVE) {
                // Same as Module 1: reuse the decompilation the GUI already computed
                // for the function under the cursor.
                if (!(currentLocation instanceof DecompilerLocation loc)) {
                    printerr("Interactive mode: open a function in the Decompiler and run this from there.");
                    return;
                }
                DecompileResults results = loc.getDecompile();
                HighFunction hf = (results == null) ? null : results.getHighFunction();
                if (hf == null) {
                    printerr("Interactive mode: no decompiler result at the current location.");
                    return;
                }
                recoverInFunction(hf, rtLog);
            } else {
                recoverAcrossProgram(rtLog);
            }
            println("\nRecovered " + renamedCount + " name(s).");
        } finally {
            currentProgram.endTransaction(txId, true);
        }
    }

    /**
     * EXERCISE 1 — filter to the relevant callsites.
     *
     * Walk the function's P-Code ({@link HighFunction#getPcodeOps()}) and keep
     * only the {@link PcodeOp#CALL} ops whose target is {@code rtLog}. For a CALL,
     * {@code op.getInput(0)} is the call target: an address Varnode equal to the
     * callee's entry point.
     */
    private List<PcodeOp> findRtLogCalls(HighFunction hf, Function rtLog) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        List<PcodeOp> calls = new ArrayList<>();
        Iterator<PcodeOpAST> ops = hf.getPcodeOps();
        while (ops.hasNext()) {
            PcodeOp op = ops.next();
            if (op.getOpcode() != PcodeOp.CALL) continue;
            Varnode target = op.getInput(0);
            if (target != null && target.isAddress()
                    && target.getAddress().equals(rtLog.getEntryPoint())) {
                calls.add(op);
            }
        }
        return calls;
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * EXERCISE 2 — trace a Varnode back through dataflow to the address it carries.
     *
     * The argument is rarely a constant at the op. Follow {@link Varnode#getDef()}
     * — the single op that produced this Varnode (the decompiler's P-Code is in
     * SSA form, so each Varnode has exactly one definition) — and step through the
     * value-preserving ops (COPY, CAST) until you land on something concrete: an
     * address Varnode, or a non-zero constant you can turn into an address with
     * {@code toAddr(...)}. Give up (return null) on any other defining op or when
     * there is no definition.
     *
     * Note this short-circuits: if the Varnode is already a constant/address it
     * returns on the first iteration without touching getDef(). That is what lets
     * the same code work under both simplification styles (see SIMPLIFICATION_STYLE)
     * — with a COPY it hops once, without one it returns immediately.
     */
    private Address traceToAddress(Varnode v) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        for (int hops = 0; v != null && hops < 16; hops++) {
            if (v.isAddress()) return v.getAddress();
            if (v.isConstant() && v.getOffset() != 0) return toAddr(v.getOffset());
            PcodeOp def = v.getDef();
            if (def == null) return null;
            switch (def.getOpcode()) {
                case PcodeOp.COPY:
                case PcodeOp.CAST:
                    v = def.getInput(0);
                    break;
                default:
                    return null;
            }
        }
        return null;
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /** PROVIDED — glue the two exercises together for one function: find the
     *  rt_log calls, trace the func argument of the first one to its string, and
     *  rename the enclosing function. (Every rt_log call here passes the same
     *  __func__, so one is enough.) */
    private void recoverInFunction(HighFunction hf, Function rtLog) {
        Function host = hf.getFunction();
        for (PcodeOp call : findRtLogCalls(hf, rtLog)) {
            if (call.getNumInputs() <= RT_LOG_FUNC_ARG) continue;
            Address strAddr = traceToAddress(call.getInput(RT_LOG_FUNC_ARG));
            if (strAddr == null) continue;
            String recovered = readCString(strAddr);
            if (recovered == null || recovered.isEmpty()) continue;
            rename(host, recovered);
            return;
        }
    }

    /** PROVIDED — batch over the whole program, but only the functions that
     *  actually call rt_log: the cross-references give that worklist directly,
     *  so it skips decompiling everything else. */
    private void recoverAcrossProgram(Function rtLog) {
        DecompInterface decomp = new DecompInterface();
        decomp.setOptions(new DecompileOptions());
        decomp.openProgram(currentProgram);
            // The decompiler doesn't hand you one fixed IR — it runs a pipeline of
            // simplification actions, and you choose how far it goes. Two worth knowing:
            //   "decompile" — the full pipeline (what the GUI and decompileFunction use).
            //                 The func pointer reaches the CALL through a COPY, so you need
            //                 dataflow tracing to follow it (that's exercise 2).
            //   "normalize" — a lighter pipeline that folds the pointer straight onto the
            //                 CALL as a plain constant: no COPY at all. The exact same
            //                 traceToAddress still works — it returns on the first hop.
            // Flip this to "normalize" and re-run: the COPY disappears, the result is
            // identical. The shape of the IR is a setting, not a fact of the binary.
        decomp.setSimplificationStyle("decompile"); // see the note on SIMPLIFICATION_STYLE
        try {
            LinkedHashMap<Address, Function> callers = new LinkedHashMap<>();
            for (Reference ref : getReferencesTo(rtLog.getEntryPoint())) {
                if (!ref.getReferenceType().isCall()) continue;
                Function caller = getFunctionContaining(ref.getFromAddress());
                if (caller == null || caller.getEntryPoint().equals(rtLog.getEntryPoint())) continue;
                callers.putIfAbsent(caller.getEntryPoint(), caller);
            }
            for (Function caller : callers.values()) {
                DecompileResults results = decomp.decompileFunction(caller, 30, monitor);
                HighFunction hf = results.getHighFunction();
                if (hf == null) continue;
                recoverInFunction(hf, rtLog);
            }
        } finally {
            decomp.dispose();
        }
    }

    /** PROVIDED — rt_log survives stripping as a dynamic import, so it is still
     *  named. As a fallback (fully stripped/renamed) it is the unique non-thunk
     *  caller of the runtime's own vfprintf. */
    private Function findRtLog() {
        var fm = currentProgram.getFunctionManager();
        for (Function f : fm.getFunctions(true))
            if (f.getName().equals("rt_log") || f.getName().equals("_rt_log")) return f;
        for (Function f : fm.getExternalFunctions())
            if (f.getName().equals("rt_log") || f.getName().equals("_rt_log")) return f;
        for (Function f : fm.getFunctions(true)) {
            if (!f.getName().equals("vfprintf")) continue;
            for (Reference ref : getReferencesTo(f.getEntryPoint())) {
                if (!ref.getReferenceType().isCall()) continue;
                Function caller = getFunctionContaining(ref.getFromAddress());
                if (caller != null && !caller.isThunk()) return caller;
            }
        }
        return null;
    }

    /** PROVIDED — pin rt_log's signature so its arguments render with the right
     *  types. Best-effort: the func argument is already a distinct CALL input
     *  without it, so recovery works either way. */
    private void pinRtLogSignature(Function rtLog) {
        Function target = rtLog.isThunk() ? rtLog.getThunkedFunction(true) : rtLog;
        if (target == null) target = rtLog;
        try {
            target.updateFunction(null,
                new ReturnParameterImpl(new VoidDataType(), currentProgram),
                FunctionUpdateType.DYNAMIC_STORAGE_ALL_PARAMS, true, SourceType.ANALYSIS,
                new ParameterImpl("level", new IntegerDataType(), currentProgram),
                new ParameterImpl("func", new PointerDataType(new CharDataType()), currentProgram),
                new ParameterImpl("fmt", new PointerDataType(new CharDataType()), currentProgram));
            target.setVarArgs(true);
        } catch (Exception e) {
            printerr("  (could not pin rt_log signature: " + e.getMessage() + " — continuing)");
        }
    }

    /** PROVIDED — read the C string at an address (defined string if Ghidra made
     *  one, else read bytes up to a NUL). */
    private String readCString(Address addr) {
        Data d = getDataAt(addr);
        if (d != null && d.getValue() instanceof String s) return s;
        StringBuilder sb = new StringBuilder();
        try {
            for (int i = 0; i < 128; i++) {
                byte b = currentProgram.getMemory().getByte(addr.add(i));
                if (b == 0) break;
                if (b < 0x20 || b > 0x7e) return null;
                sb.append((char) (b & 0xff));
            }
        } catch (Exception e) {
            return null;
        }
        return sb.length() == 0 ? null : sb.toString();
    }

    private void rename(Function f, String recovered) {
        String old = f.getName();
        try {
            f.setName(recovered, SourceType.ANALYSIS);
            println(String.format("  %s  %-20s ->  %s", f.getEntryPoint(), old, recovered));
            renamedCount++;
        } catch (Exception e) {
            printerr("  rename failed at " + f.getEntryPoint() + ": " + e.getMessage());
        }
    }
}
