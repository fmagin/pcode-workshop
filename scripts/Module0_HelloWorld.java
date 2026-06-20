//@category PCodeWorkshop

import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.Program;

/**
 * Module 0 — Hello, Ghidra.
 *
 * This script does NO analysis. Its only job is to prove your environment is
 * wired up correctly before the real modules start:
 *
 *   - the workshop {@code scripts/} folder is on the Script Manager search path,
 *   - this script shows up under the {@code PCodeWorkshop} category,
 *   - you can hit Run and see output in the Console,
 *   - you can edit the source, save, and see your change on the next Run.
 *
 * Try the exercise at the bottom of {@link #run()}: change {@code GREETING},
 * save (the editor's green check / Ctrl-S), and Run again. If the Console shows
 * your new text, you are ready for Module 1.
 */
public class Module0_HelloWorld extends GhidraScript {

    // EDIT ME: change this string, save, and re-run to confirm edits take effect.
    private static final String GREETING = "Hello from the P-Code Workshop!";

    @Override
    public void run() throws Exception {
        println(GREETING);

        Program program = currentProgram;
        if (program == null) {
            // A script can run without a program open — that's fine for a sanity check.
            println("No program is open. Open sysmond_stripped in the CodeBrowser to load one.");
            println("Environment looks good — you're ready for Module 1.");
            return;
        }

        // The handful of GhidraScript conveniences every later module leans on.
        println("Current program : " + program.getName());
        println("Language        : " + program.getLanguageID());
        println("Image base      : " + program.getImageBase());
        println("Functions       : " + program.getFunctionManager().getFunctionCount());

        // popup() opens a dialog — handy when you want a result to be impossible to miss.
        popup(GREETING + "\n\nEnvironment looks good — you're ready for Module 1.");
    }
}
