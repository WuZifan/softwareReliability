package parser;

import java.util.List;
import java.util.Map;

import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.ProcedureDeclContext;

public class ParameterVisitor extends SimpleCBaseVisitor<Void> {
	private StringBuilder ResSmt;
	private Map<String, Integer> variCount;
	
	public ParameterVisitor(VariCount variCount) {
		this.variCount = variCount.getVarCount();
		ResSmt = new StringBuilder("");
	}
	
	/** Current: multiple parametres checking **/
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
		List<FormalParamContext> paras;
		paras = ctx.formals;
		for(FormalParamContext para : paras) {
			String name = para.name.getText();
			this.ResSmt.append(this.getDeclStmt(name));
			this.variCount.put(name, 0);
//			System.out.println(ResSmt);
		}
		
		return null;
	}
	
	private String getDeclStmt(String variName) {
		StringBuilder result = new StringBuilder();
		String typeName="Int";
		result.append("(declare-fun ");
		result.append(variName + "0");
		result.append("() ");
		result.append(typeName + ")");
		result.append("\n");
		return result.toString();
	}
	
	public String getSMT(){
		return ResSmt.toString();
	}
}
