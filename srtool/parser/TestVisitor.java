package parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import parser.SimpleCParser.*;

public class TestVisitor extends SimpleCBaseVisitor<String> {
	private Map<String, ArrayList<Integer> > variCount;
	private ArrayList<Integer> IfLayer;
	private StringBuilder smtResult;
	private MyAssertVisitor assVisitor;
	private StringBuilder exprResult;
	private int inCond;
	
	public TestVisitor() {
		this.smtResult = new StringBuilder();
	}
	
	public TestVisitor(MyAssertVisitor assVisitor,VariCount variCount, String glSmt, String plSmt){
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.IfLayer = variCount.getIfLayer();
		this.smtResult = new StringBuilder();
		this.smtResult.append(glSmt);
		this.smtResult.append(plSmt);
		this.inCond = 0;
		
	}
	
	public TestVisitor(MyAssertVisitor assVisitor,VariCount variCount){
		this.assVisitor = assVisitor;
		this.variCount = variCount.getVarCount();
		this.smtResult = new StringBuilder();
		this.inCond = 0;
	}


	// 声明语句的SMT转换
	@Override
	public String visitVarDecl(VarDeclContext ctx) {
		// SMT语句结果
		StringBuilder result = new StringBuilder();
		// 只有一种类型，所以不用特地处理类型名
		// 变量名
		String variName = ctx.getChild(1).getText();
		ArrayList<Integer> status = new ArrayList<Integer>();
		status.add(1);
		status.add(0);
		// 变量名，下标初始为0
		variCount.put(variName, status);
		variName = variName+"0";
		// 编写SMT语句
		result.append(getDeclStmt(variName));
		// 调用父类
		super.visitVarDecl(ctx);
		// 拼接完整SMT语句
		smtResult.append(result.toString());
		return null;
	}

	// 赋值语句的SMT转换
	@Override
	public String visitAssignStmt(AssignStmtContext ctx) {
		// 被赋值的变量名，且取下标
		String name = ctx.getChild(0).getText();
		String variName = name + getSubscript(name);
		incSubscript(name);
		// 暂时只考虑单个数字赋值
		String num = ctx.getChild(2).getText();
		
		// not类型的assert.
		StringBuilder unnomAss=new StringBuilder();
		
		// 普通类型的asert
		StringBuilder nomoAss=new StringBuilder();
		// 赋值语句
		nomoAss.append("(assert (= "+variName+" "+num+"))\n");
		assVisitor.visitnomorAss(nomoAss.toString());
		
		// 判断是否超过限制
		unnomAss.append("(<= "+variName+" 4294967295)");
		unnomAss.append("(>= "+variName+" 0)");
		assVisitor.visitunnomAss(unnomAss.toString());

		// 只是定义超限报错，但是具体行为没有报错

		// 下标问题
		return super.visitAssignStmt(ctx);
	}

	@Override
	public String visitExpr(ExprContext ctx) {
		// TODO Auto-generated method stub
		return super.visitExpr(ctx);
	}
	
	@Override
	public String visitIfStmt(IfStmtContext ctx) {
		Map<String, ArrayList<Integer>> init = new HashMap<String, ArrayList<Integer>>();
		Map<String, ArrayList<Integer>> afif = new HashMap<String, ArrayList<Integer>>();
		String cond;
		this.variCount.putAll(init);
		
		this.IfLayer.add(this.IfLayer.size() + 1);
//		System.out.println(ctx.condition.getText());
		
		cond = super.visitExpr(ctx.condition);
		
		super.visitBlockStmt(ctx.thenBlock);
		this.variCount.putAll(afif);
		
		if(ctx.elseBlock != null) {
			super.visitBlockStmt(ctx.elseBlock);
		}
		this.IfLayer.remove(this.IfLayer.size() - 1);
		return null;
	}
	
	@Override
	public String visitTernExpr(TernExprContext ctx) {
		
		return null;
		
	}
	
	// 获取声明语句的SMT语句
	private String getDeclStmt(String variName) {
		StringBuilder result = new StringBuilder();
		String typeName="Int";
		// 编写SMT语句
		result.append("(declare-fun ");
		result.append(variName + " ");
		result.append("() ");
		result.append(typeName + ")");
		result.append("\n");
		return result.toString();
	}

	/** Get current subscripte for a specific variable **/
	private int getSubscript(String text) {
		return variCount.get(text).get(1);	
	}
	
	/** Increase the subscript while assigned **/
	private void incSubscript(String text) {
		variCount.get(text).set(1, getSubscript(text) + 1);
	}
	
	/** Remove all local variables, later use **/
	private void rmLocalVar() {
		for(Map.Entry<String, ArrayList<Integer> > iter : this.variCount.entrySet()) {
			if (iter.getValue().get(0) == 1) {
				this.variCount.remove(iter.getKey());
			}
		}
	}
	
	// 返回整个SMT
	public String getSMT(){
		return smtResult.toString();
	}
}
