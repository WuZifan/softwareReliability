package example;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.antlr.v4.runtime.Token;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.UnaryExprContext;

public class Count42sVisitor extends SimpleCBaseVisitor<String> {

	private int num42s = 0;
	private boolean inAssert = false;
	private LinkedList<String> argQue = new LinkedList<String>();

	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {
		super.visitAssignStmt(ctx);
		for (String str : this.argQue) {
			System.out.println("AssExpr:" + str);
		}
		return null;
	}

	@Override
	public String visitExpr(ExprContext ctx) {
		super.visitExpr(ctx);
		return null;
	}

	@Override
	public String visitAddExpr(AddExprContext ctx) {
		super.visitAddExpr(ctx);
		String result = null;
		if (!ctx.args.isEmpty()) {
			/*
			 */
			List<String> opsList = new ArrayList<String>();
			List<String> argList = new ArrayList<String>();
			for (Token token : ctx.ops) {
				opsList.add(token.getText());
			}
			for (MulExprContext uec : ctx.args) {
				argList.add(uec.getText());
			}
			if (!opsList.isEmpty() && !argList.isEmpty()) {
				/*
				 */
				result = getOperSMT(opsList, argList);
			}else{
				return argList.get(0);
			}

		} else {
			return null;
		}
		this.argQue.add(result);
		return null;
	}

	@Override
	public String visitMulExpr(MulExprContext ctx) {
		super.visitMulExpr(ctx);
		String result = null;
		if (!ctx.args.isEmpty()) {
			/*
			 */
			List<String> opsList = new ArrayList<String>();
			List<String> argList = new ArrayList<String>();
			for (Token token : ctx.ops) {
				opsList.add(token.getText());
			}
			for (UnaryExprContext uec : ctx.args) {
				argList.add(uec.getText());
			}
			if (!opsList.isEmpty() && !argList.isEmpty()) {
				result = getOperSMT(opsList, argList);
			}else{
				return argList.get(0);
			}
		} else {
			return null;
		}
		this.argQue.add(result);
		return null;
	}

	/**
	 * 一元操作符的使用
	 */
	@Override
	public String visitUnaryExpr(UnaryExprContext ctx) {
		super.visitUnaryExpr(ctx);
		for(Token token:ctx.ops){
			System.out.println("UnaryToken: "+token.getText());
		}
		for(int i=0;i<ctx.getChildCount();i++){
			System.out.println("UnaryChild: "+ctx.getChild(i).getText());
		}
		System.out.println("------");
		String result=null;
		List<String> opsList=new ArrayList<String>();
		List<String> argList=new ArrayList<String>();
		String oper="!~+-";
		for(int i=0;i<ctx.getChildCount();i++){
			String str=ctx.getChild(i).getText();
			if(oper.contains(str)){
				opsList.add(str);
			}else{
				argList.add(str);
			}
		}
		/*
		 */
		if(!opsList.isEmpty()){
			String arg=argList.get(0);
			arg=arg.replaceAll("[( )]","");
			try{
				Integer.valueOf(arg);
				result=getUnarySMT(opsList,arg);
			}catch(Exception e){
				arg=this.argQue.pollLast();
				result=getUnarySMT(opsList,arg);
			}
		}
		if(result!=null){
			this.argQue.add(result);
		}
		return null;
	}
	// (!(~(-(+ 1))))
	private String getUnarySMT(List<String> opsList, String arg) {
		StringBuilder result=new StringBuilder();
		for(String ops:opsList){
			result.append("("+ops+" ");
		}
		result.append(arg);
		for(int i=0;i<opsList.size();i++){
			result.append(")");
		}
		return result.toString();
	}

	/**
	 * 括号的使用
	 */
	@Override
	public String visitParenExpr(ParenExprContext ctx) {
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
		/*
		 */
		StringBuilder result = new StringBuilder();
		/*
		 */
		boolean flag = false;
		int count = 0;
		for (String str : argList) {
			try {
				Integer.valueOf(str);
			} catch (Exception e) {
				count++;
			}
		}
		/*
		 */
		if (count == this.argQue.size()) {
			flag = false;
		} else {
			/*
			 */
			flag = true;
		}

		int opsLen = opsList.size();
		result.append("(" + opsList.remove(opsLen - 1));
		if (opsList.isEmpty()) {
			result.append(getArg(argList, 0, flag) + " ");
			if (argList.isEmpty()) {
				result.append(")");
			} else {
				result.append(getArg(argList, 0, flag) + ")");
			}
		} else {
			result.append(getOperSMT(opsList, argList));
			result.append(" " + getArg(argList, 0, flag) + ")");
		}
		return result.toString();
	}

	/**
	 * 
	 * @param argList
	 * @param i
	 * @return
	 */
	private String getArg(List<String> argList, int i, boolean flag) {
		/*
		 */
		String arg = argList.remove(i);
		try {
			Integer.valueOf(arg);
			return arg;
		} catch (Exception e) {
			/*
			 */
			if (flag) {
				String last = this.argQue.pollLast();
				return last;
			} else {
				String first = this.argQue.pollFirst();
				return first;
			}
		}
	}

	public int getNum42s() {
		return num42s;
	}

	public static void main(String[] args) {
		String  str="(1)";
		String  str2="2";
		String  str3="(1+2+3)";
		System.out.println(str.replaceAll("[( )]",""));
		System.out.println(str2.replaceAll("[( )]",""));
		System.out.println(str3.replaceAll("[( )]",""));
	}
}
