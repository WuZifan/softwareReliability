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
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.UnaryExprContext;

public class Count42sVisitor3 extends SimpleCBaseVisitor<String> {

	private int num42s = 0;
	private boolean inAssert = false;
	private LinkedList<String> argQue = new LinkedList<String>();

	// private StringBuilder
	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	@Override
	public String visitExpr(ExprContext ctx) {
		return super.visitExpr(ctx);
	}

	@Override
	public String visitNumberExpr(NumberExprContext ctx) {
		if (inAssert && ctx.number.getText().equals("42")) {
			num42s++;
		}
		return null;
	}

	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {
		return super.visitAssignStmt(ctx);
	}

	@Override
	public String visitAddExpr(AddExprContext ctx) {
		String resultsub=super.visitAddExpr(ctx);
		System.out.println("AddTestResult"+resultsub);
		String result = null;
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
				for (String str : argQue) {
					System.out.println("AddQue: " + str);
				}
				result = getOperSMT(opsList, argList);
			}
		} else {
			return null;
		}
		this.argQue.add(result);
		System.out.println(result);
		return result;
	}

	@Override
	public String visitMulExpr(MulExprContext ctx) {
		String subresult=super.visitMulExpr(ctx);
		System.out.println("MulTestResult:"+subresult);
		String result = null;
		for (Token token : ctx.ops) {
			System.out.println("MulExpr: " + token.getText());
		}
		for (UnaryExprContext uec : ctx.args) {
			System.out.println("MulExpr: " + uec.getText());
		}
		if (!ctx.args.isEmpty()) {
			List<String> opsList = new ArrayList<String>();
			List<String> argList = new ArrayList<String>();
			for (Token token : ctx.ops) {
				opsList.add(token.getText());
			}
			for (UnaryExprContext uec : ctx.args) {
				argList.add(uec.getText());
			}
			if (!opsList.isEmpty() && !argList.isEmpty()) {
				for (String str : argQue) {
					System.out.println("MulQue: " + str);
				}
				result = getOperSMT(opsList, argList);
			}
		} else {
			return null;
		}

		this.argQue.add(result);
		System.out.println("MulExpr: " + result);
		return result;
	}


	/**
	 */
	@Override
	public String visitParenExpr(ParenExprContext ctx) {
		ExprContext opsList = ctx.arg;
		System.out.println("lololo");
		return super.visitParenExpr(ctx);
	}

	/**
	 * 
	 * @param opsList
	 * @param artList
	 * @return
	 */
	private String getOperSMT(List<String> opsList, List<String> argList) {
		StringBuilder result = new StringBuilder();
		int opsLen = opsList.size();
		result.append("(" + opsList.remove(opsLen - 1));
		if (opsList.isEmpty()) {
			result.append(getArg(argList, 0) + " ");
			if (argList.isEmpty()) {
				result.append(")");
			} else {
				result.append(getArg(argList, 0) + ")");
			}
		} else {
			result.append(getOperSMT(opsList, argList));
			result.append(" " + getArg(argList, 0) + ")");
		}
		return result.toString();
	}

	/**
	 * 
	 * @param argList
	 * @param i
	 * @return
	 */
	private String getArg(List<String> argList, int i) {
		for (String string : argList) {
			System.out.println("getArg: "+string);
		}
		for(String str:this.argQue){
			System.out.println("getArg: "+str);
		}
		String arg = argList.remove(i);
		try {
			Integer.valueOf(arg);
			return arg;
		} catch (Exception e) {
//			return this.argQue.pop();
			return this.argQue.pollLast();
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
		LinkedList<String> test=new LinkedList<String>();
		test.add("a");
		test.add("b");
		test.add("c");
		System.out.println(test.pollFirst());
		System.out.println(test.pollLast());
	}
}