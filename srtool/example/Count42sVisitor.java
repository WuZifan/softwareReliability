package example;

import javax.rmi.ssl.SslRMIClientSocketFactory;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.NumberExprContext;

public class Count42sVisitor extends SimpleCBaseVisitor<Void> {

	private int num42s = 0;
	private boolean inAssert = false;
	// assert(42==42);
	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
//		System.out.println(ctx.getChild(0).getText());
//		System.out.println(ctx.getChild(1).getText());
//		System.out.println(ctx.getChild(2).getText());
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	@Override
	public Void visitExpr(ExprContext ctx) {
//		System.out.println(ctx.getChildCount());
		System.out.print("Expr: ");
		System.out.println(ctx.getChild(0).getText());
		return super.visitExpr(ctx);
	}
	
	@Override
	public Void visitNumberExpr(NumberExprContext ctx) {
//		System.out.println(ctx.getChildCount());
//		System.out.println("NUmber:"+ctx.number);
//		System.out.println("number:"+ctx.number.getText());
		if(inAssert && ctx.number.getText().equals("42")) {			
			num42s++;
		}
		return null;
	}

	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		System.out.print("assign: ");
		System.out.println(ctx.getChildCount());
		System.out.println("assign:"+ctx.getChild(0).getText());
		System.out.println("assign:"+ctx.getChild(1).getText());
		System.out.println("assign:"+ctx.getChild(2).getText());
		System.out.println("assign:"+ctx.getChild(3).getText());
		return super.visitAssignStmt(ctx);
	}
	
	@Override
	public Void visitAddExpr(AddExprContext ctx) {
		System.out.println("AddExpr: "+ctx.getText());
		StringBuilder result=new StringBuilder();
		
		// 1+1+1;
		// (+ (+ 1 1) 1)
		for(int i=0;i<ctx.getChildCount();i++){
			
		}
		return super.visitAddExpr(ctx);
	}
	
	public int getNum42s() {
		return num42s;
	}

}
