package tool;
import java.io.BufferedWriter;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;

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
		String filename="example/Count42.c";
		/*
		 * Correct
		 */
		// Pased
//		String filename="tests/correct/divzero.c"; 
		// Pased. But afarid of missing the assertation in the block
//		String filename="tests/correct/if.c";
		// Error:(error "line 28 column 21: unexpected character"):(assert (= x3 (ite  ([@31,151:151='<',<29>,11:9] x0 (or ) (bvlshr 1 24)) x2 x1)))
//		String filename="tests/correct/ifelse.c";
		// (Error "line 8 column 36: invalid function application, arguments missing")
//		String filename="tests/correct/overshift.c";
		// Pased
//		String filename="tests/correct/simpleeq.c";
		// (Error "line 15 column 29: Sort mismatch at argument #2 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int")
//		String filename="tests/correct/simplelor.c";
		// Pased
//		String filename="tests/correct/simplesub.c";
		/*
		 * INCORRECT
		 */
		// (Error "line 6 column 28: Sort mismatch at argument #2 for function (declare-fun and (Bool Bool) Bool) supplied sort is Int")
//		String filename="tests/incorrect/assertfalse.c";
		// Pased
//		String filename="tests/incorrect/faildivzero.c";
//		String filename="tests/incorrect/failold.c";
//		String filename="tests/incorrect/failovershift.c.c";
//		String filename="tests/incorrect/failsimpleeq.c";
//		String filename="tests/incorrect/failsimplelor.c";
//		String filename="tests/incorrect/failsimplesub.c";
		ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
        SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		ProgramContext ctx = parser.program();
		if(parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
		Typechecker tc = new Typechecker();
		tc.visit(ctx);
		tc.resolve();
		if(tc.hasErrors()) {
			System.err.println("Errors were detected when typechecking " + filename + ":");
			for(String err : tc.getErrors()) {
				System.err.println("  " + err);
			}
			System.exit(1);
		}
		
		assert ctx.procedures.size() == 1; // For Part 1 of the coursework, this can be assumed

		VCGenerator vcgenGl = new VCGenerator(ctx, null);
		vcgenGl.generateVCGlobal();
		System.out.println();
		for(ProcedureDeclContext proc : ctx.procedures) {
			VCGenerator vcgen = new VCGenerator(null, proc);
			String vc = vcgen.generateVC().toString();
			ProcessExec process = new ProcessExec("z3", "-smt2", "-in");
			String queryResult = "";
			try {
				queryResult = process.execute(vc, TIMEOUT);
				System.out.println(queryResult);
			} catch (ProcessTimeoutException e) {
				System.out.println("UNKNOWN");
				System.exit(1);
			}
			
			if (queryResult.startsWith("sat")) {
				System.out.println("INCORRECT");
				System.exit(0);
			}
			
			if (!queryResult.startsWith("unsat")) {
				System.out.println("UNKNOWN");
				System.out.println(queryResult);
				System.exit(1);
			}
		}
		
		System.out.println("CORRECT");
		System.exit(0);
		
    }
}
