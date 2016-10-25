package example;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.antlr.v4.runtime.Token;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.UnaryExprContext;

public class Count42sVisitor extends SimpleCBaseVisitor<Void> {

	private int num42s = 0;
	private boolean inAssert = false;
	// private List<String> opraList=new ArrayList<String>();
	// private List<String> argList=new ArrayList<String>();
	private Queue<String> oprQue = new LinkedList<String>();
	private Queue<String> argQue = new LinkedList<String>();

	// private StringBuilder
	@Override
	public Void visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
		// System.out.println(ctx.getChild(0).getText());
		// System.out.println(ctx.getChild(1).getText());
		// System.out.println(ctx.getChild(2).getText());
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	@Override
	public Void visitExpr(ExprContext ctx) {
		// System.out.println(ctx.getChildCount());
		// System.out.print("Expr: ");
		// System.out.println(ctx.getChild(0).getText());
		return super.visitExpr(ctx);
	}

	@Override
	public Void visitNumberExpr(NumberExprContext ctx) {
		// System.out.println(ctx.getChildCount());
		// System.out.println("NUmber:"+ctx.number);
		// System.out.println("number:"+ctx.number.getText());
		if (inAssert && ctx.number.getText().equals("42")) {
			num42s++;
		}
		return null;
	}

	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		return super.visitAssignStmt(ctx);
	}

	@Override
	public Void visitAddExpr(AddExprContext ctx) {
		// 先进到下面一级
		super.visitAddExpr(ctx);
		// 再计算本地的内容
		String result = null;
		for (Token token : ctx.ops) {
			System.out.println("AddExpr: "+token.getText());
		}
		for (MulExprContext uec : ctx.args) {
			System.out.println("AddExpr: "+uec.getText());
		}
		// 当有多个参数时
		if (!ctx.args.isEmpty()) {
			List<String> opsList = new ArrayList<String>();
			List<String> argList = new ArrayList<String>();
			for (Token token : ctx.ops) {
				opsList.add(token.getText());
			}
			for (MulExprContext uec : ctx.args) {
				argList.add(uec.getText());
			}
			if (!opsList.isEmpty() && !argList.isEmpty()) {
				for(String str:argQue){
					System.out.println("AddQue: "+str);
				}
			result = getOperSMT(opsList, argList);
			}
		} else {
			return null;
		}

		System.out.println(result);
		return null;
	}

	@Override
	public Void visitMulExpr(MulExprContext ctx) {
		// 先进到下面一级
		// 在计算本地内容
		super.visitMulExpr(ctx);
	
		String result = null;
		for (Token token : ctx.ops) {
			System.out.println("MulExpr: "+token.getText());
		} 
		for(UnaryExprContext uec:ctx.args){
			System.out.println("MulExpr: "+uec.getText());
		 }
		// 当有多个参数时
		if (!ctx.args.isEmpty()) {
			List<String> opsList = new ArrayList<String>();
			List<String> argList = new ArrayList<String>();
			for (Token token : ctx.ops) {
				opsList.add(token.getText());
			}
			for (UnaryExprContext uec : ctx.args) {
				argList.add(uec.getText());
			}
			// 两者都不为空的情况下进入
			if (!opsList.isEmpty() && !argList.isEmpty()) {
				result = getOperSMT(opsList, argList);
			}
		} else {
			return null;
		}
		
		this.argQue.add(result);
		System.out.println("MulExpr: "+result);
		return null;
	}

	@Override
	public Void visitUnaryExpr(UnaryExprContext ctx) {
		List<Token> opsList = ctx.ops;
		AtomExprContext atomArg = ctx.arg;
		return super.visitUnaryExpr(ctx);
	}

	@Override
	public Void visitParenExpr(ParenExprContext ctx) {
		ExprContext opsList = ctx.arg;
		return super.visitParenExpr(ctx);
	}

	/**
	 * 递归的得到smt语句
	 * 
	 * @param opsList
	 * @param artList
	 * @return
	 */
	private String getOperSMT(List<String> opsList, List<String> argList) {
		StringBuilder result = new StringBuilder();
		int opsLen = opsList.size();
		// 取出最后一个操作符
		result.append("(" + opsList.remove(opsLen - 1));
		// 判断是否还有操作符
		if (opsList.isEmpty()) {
			// 若没有其他操作符,取出头两个被操作数
			result.append(getArg(argList, 0) + " ");
			result.append(getArg(argList, 0) + ")");
		} else {
			// 若还有其他操作符,递归
			result.append(getOperSMT(opsList, argList));
			// 在之后放上另一个操作数
			result.append(" " + getArg(argList, 0) + ")");
		}
		return result.toString();
	}

	/**
	 * 拿到操作数
	 * 
	 * @param argList
	 * @param i
	 * @return
	 */
	private String getArg(List<String> argList, int i) {
		String arg = argList.remove(i);
		try {
			// 判断这个字符串是否是整数
			Integer.valueOf(arg);
			// 如果是整数,返回本字符串
			return arg;
		} catch (Exception e) {
			// 不然就返回成员变量 argQue的第一个成员
			return this.argQue.poll();
		}
	}

	private List<String> getNumList(String mulStmt) {
		List<String> list = new ArrayList<String>();
		String rule = "\\d+";
		Pattern p = Pattern.compile(rule);
		Matcher ma = p.matcher(mulStmt);
		while (ma.find()) {
			list.add(ma.group());
		}
		return list;
	}

	public int getNum42s() {
		return num42s;
	}

	public static void main(String[] args) {
		List<String> list = new ArrayList<String>();
		list.add("a");
		list.add("b");
		System.out.println(list.remove(0));
		System.out.println(list.remove(0));
	}
}

// @Override
// public Void visitMulExpr(MulExprContext ctx) {
// // 先进行更高级的表达式
// super.visitMulExpr(ctx);
// // 结果SMT语句
// StringBuilder mulSMT=new StringBuilder();
// // 拿到这句表达式
// String mulStmt=ctx.getText();
// // 去除字符串
// mulStmt.trim();
// // 按顺序，拿到所有运算符
// List<Token> opsList=ctx.ops;
// // 按顺序，拿到所有的操作数
// List<String> numList=getNumList(mulStmt);
//
// if(opsList.size()!=0){
// // 拼接前面的内容
// for(int i=0;i<opsList.size();i++){
// // 形成 (* 1 (% 2 (/ 3 这样的String
// mulSMT.append("("+opsList.get(i).getText()+" "+numList.get(i)+" ");
// }
// // 拼接最后一个操作数
// mulSMT.append(numList.get(opsList.size()));
// // 拼接最后的括号
// for(int i=0; i<opsList.size();i++){
// mulSMT.append(")");
// }
// }else{
//// mulSMT.append("(* "+mulStmt+" 1)");
// mulSMT.append(mulStmt);
// }
// System.out.println(mulSMT.toString());
//
// return null;
// }
