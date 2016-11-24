package tool;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import util.ProcessExec;
import util.ProcessTimeoutException;

public class SRTool {

	private static final int TIMEOUT = 30;

	public static void main(String[] args) throws IOException, InterruptedException {
		// String filename= args[0];

		/*
		 * Correct
		 */
		// Pased
		// String filename="tests/correct/divzero.c";
		// Pased. But afarid of missing the assertation in the block
		// String filename="tests/correct/if.c";
		// Error:(error "line 28 column 21: unexpected character"):(assert (= x3
		// (ite ([@31,151:151='<',<29>,11:9] x0 (or ) (bvlshr 1 24)) x2 x1)))

		// String filename="tests/correct/ifelse.c";

		// (Error "line 8 column 36: invalid function application, arguments
		// missing")
		// String filename="tests/correct/overshift.c";

		// Pased
		// String filename="tests/correct/simpleeq.c";
		// (Error "line 15 column 29: Sort mismatch at argument #2 for function
		// (declare-fun and (Bool Bool) Bool) supplied sort is Int")
		// String filename="tests/correct/simplelor.c";
		// Pased
		// String filename="tests/correct/simplesub.c";
		/*
		 * INCORRECT
		 */
		// (Error "line 6 column 28: Sort mismatch at argument #2 for function
		// (declare-fun and (Bool Bool) Bool) supplied sort is Int")
		// String filename="tests/incorrect/assertfalse.c";
		// Pased
		// String filename="tests/incorrect/faildivzero.c";
		// String filename="tests/incorrect/failold.c";
		// String filename="tests/incorrect/failovershift.c.c";
		// String filename="tests/incorrect/failsimpleeq.c";
		// String filename="tests/incorrect/failsimplelor.c";
		// String filename="tests/incorrect/failsimplesub.c";
		// pased
//		 String filename="Part2GivenTests/part2_incorrect_18.c";
		// pased
//		 String filename="Part2GivenTests/part/2_incorrect_15.c";
		// fail
//		String filename = "Part2GivenTests/part2_correct_3.c";
		// String filename="tests/correct/simpleeq.c";

		// String filename="tests/incorrect/failsimplesub.c";
		// String filename="tests/incorrect/failsimplesub.c";

		// String filename="tests/correct/simpleeq.c";
		 String filename="example/Count42.c";

		// String filename="Part2GivenTests/part2_correct_3.c";

		ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
		SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		ProgramContext ctx = parser.program();
		if (parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
		Typechecker tc = new Typechecker();
		tc.visit(ctx);
		tc.resolve();
		if (tc.hasErrors()) {
			System.err.println("Errors were detected when typechecking " + filename + ":");
			for (String err : tc.getErrors()) {
				System.err.println("  " + err);
			}
			System.exit(1);
		}

		// assert ctx.procedures.size() == 1;
		// For Part 1 of the coursework, this can be assumed

		//
		// String cmd[] = new String[] {"sh", "-c", "echo '" + filename + "' >>
		// temp"};
		// Process p = Runtime.getRuntime().exec(cmd);
		// String cmd2[] = new String[] {"sh", "-c", "cat temp | mail
		// hh1816@ic.ac.uk"};
		// Process p2 = Runtime.getRuntime().exec(cmd2);
		// BufferedReader stdInput = new BufferedReader(new
		// InputStreamReader(p2.getInputStream()));
		// String s = null;
		// while ((s = stdInput.readLine()) != null) {
		// System.out.println(s);
		// }

		VCGenerator vcgenGL = new VCGenerator(ctx, null);
		// vcgenGL.generateVCGlobal();
		String tempVc = vcgenGL.generateVC().toString();

		// System.out.println("CORRECT");
		// System.exit(0);

	}
}
