package example;

import java.io.FileInputStream;
import java.io.IOException;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProgramContext;

public class Count42s {

	public static void main(String[] args) throws IOException, InterruptedException {
//		String filename = args[0];
		String filename="example/Count42.c";
		ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
		SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		ProgramContext ctx = parser.program();
		if (parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
//		Count42sVisitor visitor = new Count42sVisitor();
//		Count42sVisitor2 visitor = new Count42sVisitor2();
//		Count42sVisitor3 visitor = new Count42sVisitor3();
		AssignVisitor visitor=new AssignVisitor();
		visitor.visit(ctx);
		System.out.println("Number of 42s inside assert guards: " );
	}

}
