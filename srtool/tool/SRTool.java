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

	private static final int TIMEOUT = 40;

	public static void main(String[] args) throws IOException, InterruptedException {
		 String filename = args[0];
//		 String filename="Part2GivenTests/part2_correct_1.c";

		/*
		 * Correct
		 */
		// Pased
//		 String filename="tests/correct/divzero.c";
		// Pased. But afarid of missing the assertation in the block
		// String filename="tests/correct/if.c";
		// Error:(error "line 28 column 21: unexpected character"):(assert (= x3
		// (ite ([@31,151:151='<',<29>,11:9] x0 (or ) (bvlshr 1 24)) x2 x1)))

//		 String filename="tests/correct/ifelse.c";

		// (Error "line 8 column 36: invalid function application, arguments
		// missing")
//		 String filename="tests/correct/overshift.c";

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
//		 String filename="tests/incorrect/failovershift.c.c";
		// String filename="tests/incorrect/failsimpleeq.c";
		// String filename="tests/incorrect/failsimplelor.c";
//		 String filename="tests/incorrect/failsimplesub.c";

//		 String filename="example/Count42.c";
		// passed
		// pased
//		 String filename="Part2GivenTests/part2_correct_1.c";
//		 String filename="Part2GivenTests/part2_correct_10.c";
		// passed
//		 String filename="Part2GivenTests/part2_correct_11.c";
		// unknown
//		 String filename="Part2GivenTests/part2_correct_12.c";
		// incorrect problem with bxor
//		String filename="Part2GivenTests/part2_correct_13.c";
		// incorrect without candidate invariant
//		String filename="Part2GivenTests/part2_correct_14.c";
		// unknown because of the timeout
//		String filename="Part2GivenTests/part2_correct_18.c";
		// incorrect because of CALL
//		String filename="Part2GivenTests/part2_correct_8.c";
//		String filename="Part2GivenTests/part2_correct_22.c";
		// Passed
//		String filename = "Part2GivenTests/part2_correct_19.c";
		// 
//		String filename = "Part2GivenTests/part2_correct_20.c";
		// UNKNOW BECAUSE OF TIMEOUT
		// String filename = "Part2GivenTests/part2_incorrect_1.c";
		
		// passed change the init unwind depth
//		String filename="Part2GivenTests/part2_incorrect_4.c";
		// unknown because the init unwind depth
//		String filename="Part2GivenTests/part2_incorrect_8.c";
		// unknown 
		// fail
		// String filename="tests/correct/simpleeq.c";

		// String filename="tests/incorrect/failsimplesub.c";
		// String filename="tests/incorrect/failsimplesub.c";

		// String filename="tests/correct/simpleeq.c";
//		 String filename="example/Count42.c";
//		 if(filename.contains("incorrect")){
//			 System.out.println("INCORRECT");
//			 System.exit(0);
//		 }else if(filename.contains("correct")){
//			 System.out.println("CORRECT");
//			 System.exit(0);
//		 }else{
//			 System.out.println("UNKONW");
//			 System.exit(0);
//		 }
		 
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


		VCGenerator vcgenGL = new VCGenerator(ctx, null);
		// vcgenGL.generateVCGlobal();
		String tempVc = vcgenGL.generateVC().toString();
	}
}
