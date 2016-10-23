package example;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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
//	private StringBuilder 
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
		// 先进行更高级的表达式
		super.visitMulExpr(ctx);
		// 结果SMT语句
		StringBuilder mulSMT=new StringBuilder();
		// 拿到这句表达式
		String mulStmt=ctx.getText();
		// 去除字符串
		mulStmt.trim();
		// 按顺序，拿到所有运算符
		List<Token> opsList=ctx.ops;
		// 按顺序，拿到所有的操作数
		List<String> numList=getNumList(mulStmt);

		if(opsList.size()!=0){
			// 拼接前面的内容
			for(int i=0;i<opsList.size();i++){
				// 形成  (* 1 (% 2 (/ 3 这样的String
				mulSMT.append("("+opsList.get(i)+" "+numList.get(i)+" ");
			}
			// 拼接最后一个操作数
			mulSMT.append(numList.get(opsList.size()));
			// 拼接最后的括号
			for(int i=0; i<opsList.size();i++){
				mulSMT.append(")");
			}
		}else{
			mulSMT.append("(* "+mulStmt+" 1)");
		}
		return null;
	}
	
	private List<String> getNumList(String mulStmt) {
		List<String> list=new ArrayList<String>();
		String rule="\\d+";
		Pattern p=Pattern.compile(rule);
		Matcher ma=p.matcher(rule);
		while(ma.find()){
			list.add(ma.group());
		}
		return list;
	}

	public int getNum42s() {
		return num42s;
	}
	
	
	public static void main(String[] args) {
		String str="22*33/44%55";
		String rule="\\d+";
		Pattern p=Pattern.compile(rule);
		Matcher ma=p.matcher(str);
		while(ma.find()){
			System.out.println(ma.group());
		}
	}
}
