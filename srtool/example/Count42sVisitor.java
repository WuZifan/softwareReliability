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

	// Assert语句
	@Override
	public String visitAssertStmt(AssertStmtContext ctx) {
		inAssert = true;
		super.visitAssertStmt(ctx);
		inAssert = false;
		return null;
	}

	// 赋值语句
	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {
		super.visitAssignStmt(ctx);
		for (String str : this.argQue) {
			System.out.println("AssExpr:" + str);
		}
		return null;
	}

	// 表达式语句
	@Override
	public String visitExpr(ExprContext ctx) {
		super.visitExpr(ctx);
		return null;
	}

	// 加法语句
	@Override
	public String visitAddExpr(AddExprContext ctx) {
		// 先进到下面一级,再计算本地的内容
		super.visitAddExpr(ctx);
		// 最后存储SMT的对象
		String result = null;
		// 当有多个参数时
		if (!ctx.args.isEmpty()) {
			/*
			 * 从ctx.ops中获取所有的操作符 从ctx.args中获取所有的被操作数
			 */
			List<String> opsList = new ArrayList<String>();
			List<String> argList = new ArrayList<String>();
			for (Token token : ctx.ops) {
				opsList.add(token.getText());
			}
			for (MulExprContext uec : ctx.args) {
				argList.add(uec.getText());
			}
			// 当被操作符以及被操作数都非空的情况下
			if (!opsList.isEmpty() && !argList.isEmpty()) {
				/*
				 * 将操作数的集合和被操作数的集合都放getOperSMT方法中 以获得SMT语句
				 */
				result = getOperSMT(opsList, argList);
			}else{
				// 此时表示只有操作数，没有操作符
				return argList.get(0);
			}

		} else {
			// 当操作数为空时，返回null。
			return null;
		}
		// 将返回的SMT语句放入成员变量中，以供下次使用
		this.argQue.add(result);
		return null;
	}

	@Override
	public String visitMulExpr(MulExprContext ctx) {
		// 先进到下面一级，再计算本地内容
		super.visitMulExpr(ctx);
		// 存储结果的SMT语句
		String result = null;
		// 当有多个参数时
		if (!ctx.args.isEmpty()) {
			/*
			 * 获取所有的操作数和操作符
			 */
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
			}else{
				// 此时表示只有操作数，没有操作符
				return argList.get(0);
			}
		} else {
			// 若为空，返回null
			return null;
		}
		// 将结果加入成员变量，以供下次使用
		this.argQue.add(result);
		return null;
	}

	/**
	 * 一元操作符的使用
	 */
	@Override
	public String visitUnaryExpr(UnaryExprContext ctx) {
		// 先执行下一级
		super.visitUnaryExpr(ctx);
		for(Token token:ctx.ops){
			System.out.println("UnaryToken: "+token.getText());
		}
		for(int i=0;i<ctx.getChildCount();i++){
			System.out.println("UnaryChild: "+ctx.getChild(i).getText());
		}
		System.out.println("------");
		/////////////////////////////////
		String result=null;
		List<String> opsList=new ArrayList<String>();
		List<String> argList=new ArrayList<String>();
		String oper="!~+-";
		// 得到所有的操作符与被操作数
		for(int i=0;i<ctx.getChildCount();i++){
			String str=ctx.getChild(i).getText();
			if(oper.contains(str)){
				opsList.add(str);
			}else{
				argList.add(str);
			}
		}
		/*
		 *  操作符空   操作符不空
		 *  操作数为无括号数字  操作数为数字但有括号  操作数为有括号表达式
		 *  
		 *  操作符为空时，不用处理
		 *  操作符不为空时：
		 *  	操作数为数字/有括号纯数字：将括号去掉，然后把所有的操作符都添加上去
		 * 	操作数为有括号表达式时，从argQue中pop出一个，然后将所有的操作符添加上去。
		 */
		if(!opsList.isEmpty()){
			// 一元操作 只有一个被操作数
			String arg=argList.get(0);
			// 拿掉括号
			arg=arg.replaceAll("[( )]","");
			try{
				// 如果是数字
				Integer.valueOf(arg);
				result=getUnarySMT(opsList,arg);
			}catch(Exception e){
				// 如果不是数字
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
		// 姑且什么也不做
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
		 * 传入参数为操作符和操作数
		 */
		// 存放SMT语句的对象
		StringBuilder result = new StringBuilder();
		/*
		 * 判定是poll还是pop的标志
		 */
		boolean flag = false;
		int count = 0;
		// 统计操作数中的非数字量
		for (String str : argList) {
			try {
				Integer.valueOf(str);
			} catch (Exception e) {
				count++;
			}
		}
		/*
		 * 如果操作数中的非数字量和存储SMT语句的成员变量的size相同 说明成员变量里的内容需要全部被放在这个SMT中，
		 * 则需要以poll的形式(先进先出)拿出
		 */
		if (count == this.argQue.size()) {
			// 用poll
			flag = false;
		} else {
			/*
			 * 不然，就要用pop的形式拿出
			 */
			// 用pop
			flag = true;
		}

		// 取出最后一个操作符
		int opsLen = opsList.size();
		result.append("(" + opsList.remove(opsLen - 1));
		// 判断是否还有操作符
		if (opsList.isEmpty()) {
			// 若没有其他操作符,取出头两个被操作数
			result.append(getArg(argList, 0, flag) + " ");
			// 如果只有一个操作数
			if (argList.isEmpty()) {
				result.append(")");
			} else {
				result.append(getArg(argList, 0, flag) + ")");
			}
		} else {
			// 若还有其他操作符,递归
			result.append(getOperSMT(opsList, argList));
			// 在之后放上另一个操作数
			result.append(" " + getArg(argList, 0, flag) + ")");
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
	private String getArg(List<String> argList, int i, boolean flag) {
		/*
		 * 从List中取出操作数，并删除List中的记录
		 */
		String arg = argList.remove(i);
		try {
			// 判断这个字符串是否是数字
			Integer.valueOf(arg);
			// 如果是整数,返回本字符串
			return arg;
		} catch (Exception e) {
			// 如果资格字符串不是数字
			/*
			 * 根据之前的情况，判定拿出内容的方法
			 */
			if (flag) {
				// 这个是pop
				String last = this.argQue.pollLast();
				return last;
			} else {
				// 这个是poll
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
