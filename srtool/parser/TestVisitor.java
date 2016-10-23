package parser;

import java.util.HashMap;
import java.util.Map;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.VarDeclContext;

public class TestVisitor extends SimpleCBaseVisitor<Void> {
	private static Map<String, Integer> variCount = new HashMap<String, Integer>();
	private StringBuilder smtResult = new StringBuilder();
	private MyAssertVisitor assVisitor;
	
	public TestVisitor() {
	}
	
	public TestVisitor(MyAssertVisitor assVisitor){
		this.assVisitor=assVisitor;
	}

	// 声明语句的SMT转换
	@Override
	public Void visitVarDecl(VarDeclContext ctx) {
		// SMT语句结果
		StringBuilder result = new StringBuilder();
		// 只有一种类型，所以不用特地处理类型名
		// 变量名
		String variName = ctx.getChild(1).getText();
		// 变量名，下标初始为0
		variCount.put(variName, 0);
		variName=variName+"0";
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
	public Void visitAssignStmt(AssignStmtContext ctx) {
		// 被赋值的变量名，且取下标
		String variName = getSubscript(ctx.getChild(0).getText());
		
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
	public Void visitExpr(ExprContext ctx) {
		// TODO Auto-generated method stub
		return super.visitExpr(ctx);
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

	// 取得变量的下标
	private String getSubscript(String text) {
		// 获得下标
		int subScript = variCount.get(text);
		// 下标更新
		int nextSubscript = subScript + 1;
		// 重新声明新的变量,变量名+新下标
		String newDecl=getDeclStmt(text+nextSubscript);
		// 把变量名+新下标重新塞入Map
		variCount.put(text, new Integer(nextSubscript));
		// 添加到整段SMT语句中
		smtResult.append(newDecl);
		// 返回变量名+原下标
		return text + subScript;
	}
	
	// 返回整个SMT
	public String getSMT(){
		return smtResult.toString();
	}
}
