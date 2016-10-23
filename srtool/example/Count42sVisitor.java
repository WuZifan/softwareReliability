package example;

import java.util.List;

import org.antlr.v4.runtime.Token;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;

public class Count42sVisitor extends SimpleCBaseVisitor<Void> {

	private int num42s = 0;
	private boolean inAssert = false;
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
		super.visitAddExpr(ctx);
		System.out.println("AddExpr: CTX=   "+ctx.getText());
		StringBuilder result=new StringBuilder();
//		String[] addNum=ctx.getText().split("+");
//		// 1+1+1;
//		// (+ (+ 1 1) 1)
//		for(int i=0;i<addNum.length;i++){
//			System.out.println(addNum[i]);
//		}
		return null;
	}
	
	@Override
	public Void visitMulExpr(MulExprContext ctx) {
		super.visitMulExpr(ctx);
		StringBuilder mulSMT=new StringBuilder();
		String mulStmt=ctx.getText();
		mulStmt.trim();
		List<Token> list=ctx.ops;
		for (Token token : list) {
			System.out.println(token.getText());
		}
		String[] mulNum=ctx.getText().split("*|/|%");
		System.out.println("nulNum Length: "+mulNum.length);
		System.out.println("Mul: "+ctx.getText());
		if(mulStmt.contains("*")){
			
		}else{
			mulSMT.append("(* "+mulStmt+" 1)");
		}
		return null;
	}
	
	
	
	public int getNum42s() {
		return num42s;
	}

}
