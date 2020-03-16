/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/* Inspired by org.alloytools.alloy.application/src/main/java/edu/mit/csail/sdg/alloy4whole/ExampleUsingTheCompiler */

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Module;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;


public final class RunAlloy {

    /*
     * Execute a command in a file. This method parses the file, then
     * execute the specified command.
     */
    public static void main(String[] args) throws Err {

        if (args.length != 2) {
            System.out.println("RunAlloy module.als property");
            System.exit(1);
        }

        String filename = args[0];
        String property = args[1];
        
        Module world = null;
        try {
            world = CompUtil.parseEverything_fromFile(null, null, filename);
        } catch (Err e) {
            System.err.println("Load failed at " + e.pos);
            System.exit(1);
        }

        // Choose some default options for how you want to execute the commands
        A4Options options = new A4Options();
        options.solver = A4Options.SatSolver.SAT4J;

        boolean foundprop = false;
        for (Command command : world.getAllCommands()) {
            if (command.label.equals(property)) {
                foundprop = true;
                A4Solution ans = TranslateAlloyToKodkod.execute_command(null, world.getAllReachableSigs(), command, options);
                if (command.check) { // check predicate
                    if (ans.satisfiable()) {
                        System.out.println("Counterexample found. Assertion is invalid.");
                    } else {
                        System.out.println("No counterexample found. Assertion may be valid.");
                    }
                } else { // run predicate
                    if (ans.satisfiable()) {
                        System.out.println("Instance found. Predicate is consistent.");
                    } else {
                        System.out.println("No instance found. Predicate may be inconsistent..");
                    }
                }
            }
        }
        if (! foundprop) {
            System.err.println("Property "+property+" not found.");
            System.exit(1);
        }
    }
}
