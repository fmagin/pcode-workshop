//@category PCodeWorkshop

import ghidra.app.decompiler.DecompInterface;
import ghidra.app.decompiler.DecompileOptions;
import ghidra.app.decompiler.DecompileResults;
import ghidra.app.decompiler.DecompilerLocation;
import ghidra.app.script.GhidraScript;
import ghidra.program.model.address.Address;
import ghidra.program.model.listing.CodeUnit;
import ghidra.program.model.listing.Function;
import ghidra.program.model.pcode.HighFunction;
import ghidra.program.model.pcode.PcodeOp;
import ghidra.program.model.pcode.PcodeOpAST;
import ghidra.program.model.pcode.Varnode;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

/**
 * Module 1 — Decode inline {@code TaggedString}s.
 *
 * This is the workshop's first script, so the real lesson is mechanical, not
 * clever:
 *
 *   1. How to get a decompilation to work with — either the one the GUI has
 *      ALREADY computed (from the {@link DecompilerLocation} under the cursor),
 *      or one you run yourself with a {@link DecompInterface}.
 *   2. How to walk that decompilation's P-Code: every op, every input Varnode.
 *
 * The thing you extract happens to be a string, but decoding it is the easy
 * part and is provided for you ({@link #decodeInlineTaggedString}). The runtime's
 * {@code TaggedString} is a value type — a single 64-bit word, never a real
 * pointer — so Ghidra auto-creates no cross-references and the strings are
 * invisible in the listing. For the short (length 1..7) form the characters are
 * packed straight into the word, and {@code TAGGED_STRING("...")} folds at
 * compile time into one immediate. On AArch64 that immediate is built from a
 * {@code movz}/{@code movk} chain — but you never redo that arithmetic by hand:
 * by the time you see P-Code, the constant is already folded and sitting at the
 * op as a single constant Varnode. So all you need to do is find those constants.
 */
public class Module1_InlineStrings extends GhidraScript {

    // false: scan every function in the program (the demo / batch run).
    // true:  decode only the function under the decompiler cursor.
    private static final boolean INTERACTIVE = false;

    private int decodedCount = 0;

    @Override
    public void run() throws Exception {
        int txId = currentProgram.startTransaction("Module1: label inline TaggedStrings");
        try {
            if (INTERACTIVE) {
                // --- Way 1: reuse the decompilation the GUI already has ---
                // When this script is launched from the Decompiler window, the
                // current location IS a DecompilerLocation, and it carries the
                // DecompileResults Ghidra computed to render the view. No need to
                // run the decompiler again — just take its HighFunction.
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
                report(hf.getFunction(), scanFunction(hf));
            } else {
                // --- Way 2: drive the decompiler yourself, over the whole program ---
                scanAllFunctions();
            }
            println("\nDecoded " + decodedCount + " inline TaggedString(s).");
        } finally {
            currentProgram.endTransaction(txId, true);
        }
    }

    /**
     * EXERCISE 1 — walk one decompiled function's P-Code and collect every inline
     * TaggedString constant.
     *
     * A {@link HighFunction} hands you its P-Code ops via {@link HighFunction#getPcodeOps()}.
     * Each {@link PcodeOp} has input Varnodes ({@link PcodeOp#getInputs()}); a
     * folded immediate shows up as a Varnode for which {@link Varnode#isConstant()}
     * is true, and {@link Varnode#getOffset()} is its 64-bit value. Feed that value
     * to {@link #decodeInlineTaggedString} (provided) and keep the non-null results.
     * Use {@code op.getSeqnum().getTarget()} for the address to report a hit at.
     */
    private List<Hit> scanFunction(HighFunction hf) {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        List<Hit> hits = new ArrayList<>();
        Iterator<PcodeOpAST> ops = hf.getPcodeOps();
        while (ops.hasNext()) {
            PcodeOp op = ops.next();
            for (Varnode in : op.getInputs()) {
                if (!in.isConstant()) continue;
                String decoded = decodeInlineTaggedString(in.getOffset());
                if (decoded != null) {
                    hits.add(new Hit(op.getSeqnum().getTarget(), in.getOffset(), decoded));
                }
            }
        }
        return hits;
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    /**
     * EXERCISE 2 — run the scan over every function in the program.
     *
     * Interactive mode handed you a ready-made HighFunction from the GUI. In batch
     * there is no cursor and nothing is pre-decompiled, so you open your own
     * {@link DecompInterface} against {@code currentProgram} and decompile each
     * function yourself ({@code decomp.decompileFunction(f, 30, monitor)}), then
     * reuse {@link #scanFunction} and {@link #report}. Skip thunks and externals,
     * and dispose the interface when done.
     */
    private void scanAllFunctions() throws Exception {
        // P_CODE_WORKSHOP_PARTICIPANT_BEGIN
        DecompInterface decomp = new DecompInterface();
        decomp.setOptions(new DecompileOptions());
        decomp.openProgram(currentProgram);
        try {
            for (Function f : currentProgram.getFunctionManager().getFunctions(true)) {
                if (f.isThunk() || f.isExternal()) continue;
                DecompileResults results = decomp.decompileFunction(f, 30, monitor);
                HighFunction hf = results.getHighFunction();
                if (hf == null) continue;
                report(f, scanFunction(hf));
            }
        } finally {
            decomp.dispose();
        }
        // P_CODE_WORKSHOP_PARTICIPANT_END
    }

    private record Hit(Address at, long value, String decoded) {}

    /**
     * PROVIDED — decode an inline {@code TaggedString} out of a folded 64-bit
     * constant.
     *
     * Layout (see {@code miniobj.h}):
     *   - the top byte (bits [63:56]) is the length, always 1..7 for the inline
     *     form, never 0;
     *   - the next {@code len} bytes, most-significant first, are the characters,
     *     packed into bits [55:0];
     *   - the remaining low bytes are zero padding.
     *
     * Pointer-form strings (length 8..255) are NOT inline — their low 56 bits are
     * a pointer into {@code tagged_string_blob[]} — so anything with a length tag
     * outside 1..7 is rejected here (a later module resolves those).
     *
     * @return the decoded string, or {@code null} if {@code value} is not a
     *         plausible inline TaggedString.
     */
    private String decodeInlineTaggedString(long value) {
        int len = (int) ((value >>> 56) & 0xffL);
        if (len < 1 || len > 7) return null;
        StringBuilder sb = new StringBuilder(len);
        for (int i = 0; i < 7; i++) {
            int b = (int) ((value >>> (48 - 8 * i)) & 0xffL);
            if (i < len) {
                if (b < 0x20 || b > 0x7e) return null; // not printable -> not a string
                sb.append((char) b);
            } else if (b != 0) {
                return null; // bytes below the characters must be zero padding
            }
        }
        return sb.toString();
    }

    /** PROVIDED — print each hit and drop a PRE comment at the site so the
     *  constant reads as text in BOTH the listing and the decompiler. (PRE is the
     *  comment type the decompiler renders by default; EOL comments show only in the
     *  listing — the decompiler's COMMENTEOL display option defaults to off.) */
    private void report(Function f, List<Hit> hits) {
        if (hits.isEmpty()) return;
        println(f.getName() + " @ " + f.getEntryPoint() + ":");
        for (Hit h : hits) {
            println(String.format("  %s  0x%016x  -> \"%s\"", h.at(), h.value(), h.decoded()));
            annotate(h);
            decodedCount++;
        }
    }

    private void annotate(Hit h) {
        CodeUnit cu = currentProgram.getListing().getCodeUnitAt(h.at());
        if (cu == null) return;
        String tag = "TaggedString: \"" + h.decoded() + "\"";
        String existing = cu.getComment(CodeUnit.PRE_COMMENT);
        if (existing == null) {
            cu.setComment(CodeUnit.PRE_COMMENT, tag);
        } else if (!existing.contains(tag)) {
            cu.setComment(CodeUnit.PRE_COMMENT, existing + "  " + tag);
        }
    }
}
