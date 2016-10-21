package example;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.NumberExprContext;

public class Count42sVisitor extends SimpleCBaseVisitor<Void> {

	private int num42s = 0;
	private boolean inAssert = false;
	
	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	@Override
	public Void visitNumberExpr(NumberExprContext ctx) {
		if(inAssert && ctx.number.getText().equals("42")) {
			num42s++;
		}
		return null;
	}

	public int getNum42s() {
		return num42s;
	}

}
