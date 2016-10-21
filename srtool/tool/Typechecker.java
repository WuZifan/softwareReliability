package tool;
import java.util.*;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.CallStmtContext;
import parser.SimpleCParser.EnsuresContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.OldExprContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.VarDeclContext;

public class Typechecker extends SimpleCBaseVisitor<Void> {

	private Map<String, Integer> expectedProcedures = new HashMap<>();

	private Map<String, Integer> actualProcedures = new HashMap<>();

	private Set<String> globals = new HashSet<>();

	private Set<String> parameters = null;
	
	private Deque<Set<String>> locals = null;

	private List<String> errors = new ArrayList<String>();
	
	private boolean inEnsures = false;

	@Override
	public Void visitProgram(ProgramContext ctx) {
		globals.addAll(ctx.globals.stream().map(varDecl -> varDecl.name.getText()).collect(Collectors.toList()));
		ctx.procedures.forEach(this::visit);
		return null;
	}

	@Override
	public Void visitVarDecl(VarDeclContext ctx) {
		checkNameNotInScope(ctx.name);
		locals.peekFirst().add(ctx.name.getText());
		return super.visitVarDecl(ctx);
	}

	@Override
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
		String name = ctx.name.getText();
		if (actualProcedures.containsKey(name)) {
			error("Redeclaration of procedure " + name + " at line " + ctx.name.getLine());
		}
		actualProcedures.put(name, ctx.formals.size());
		assert parameters == null;
		parameters = new HashSet<>();
		assert locals == null;
		locals = new LinkedList<>();
		locals.addFirst(new HashSet<>());
		for(FormalParamContext fp : ctx.formals) {
			checkNameNotInScope(fp.name);
			parameters.add(fp.name.getText());
		}
		Void result = super.visitProcedureDecl(ctx);
		locals = null;
		parameters = null;
		return result;
	}

	@Override
	public Void visitBlockStmt(SimpleCParser.BlockStmtContext ctx) {
		locals.addFirst(new HashSet<>());
		super.visitBlockStmt(ctx);
		locals.removeFirst();
		return null;
	}

	@Override
	public Void visitEnsures(EnsuresContext ctx) {
		inEnsures = true;
		Void result = super.visitEnsures(ctx);
		inEnsures = false;
		return result;
	}

	@Override
	public Void visitResultExpr(ResultExprContext ctx) {
		if(!inEnsures) {
			error("'\\result' appears outside 'ensures' clause at line " + ctx.resultTok.getLine());
		}
		return super.visitResultExpr(ctx);
	}

	@Override
	public Void visitOldExpr(OldExprContext ctx) {
		if(!globals.contains(ctx.arg.getText())) {
			error("'\\old' applied to non-global variable at line " + ctx.oldTok.getLine());
		}
		return super.visitOldExpr(ctx);
	}
	
	@Override
	public Void visitCallStmt(CallStmtContext ctx) {
		String name = ctx.callee.getText();
		int numArgs = ctx.actuals.size();
		if(expectedProcedures.containsKey(name) && expectedProcedures.get(name) != numArgs) {
			error("Procedure " + name + " is called inconsistently at line " + ctx.callee.getLine());
		}
		expectedProcedures.put(name, numArgs);
		checkAssignmentToVar(ctx.lhs);
		return super.visitCallStmt(ctx);
	}

	@Override
	public Void visitVarrefExpr(SimpleCParser.VarrefExprContext ctx) {
		checkNameInScope(ctx.name);
		return super.visitVarrefExpr(ctx);
	}

	private void checkNameInScope(Token nameToken) {
		if(!nameIsInScope(nameToken)) {
			error("Undefined variable " + nameToken.getText() + " referenced at line " + nameToken.getLine());
		}
	}

	private void checkNameNotInScope(Token nameToken) {
		if(nameIsInScope(nameToken)) {
			error("Redeclaration of " + nameToken.getText() + " at line " + nameToken.getLine());
		}
	}

	private boolean nameIsInScope(Token nameToken) {
		String name = nameToken.getText();
		return isLocal(name) || parameters.contains(name) || globals.contains(name);
	}

	boolean isLocal(String name) {
		return locals.stream().anyMatch(x -> x.contains(name));
	}

	public void resolve() {
		for(String callee : expectedProcedures.keySet()) {
			if(actualProcedures.containsKey(callee)) {
				if(expectedProcedures.get(callee) != actualProcedures.get(callee)) {
					error("Procedure " + callee + " invoked with " + expectedProcedures.get(callee) + " arguments, but " + actualProcedures.get(callee) + " were expected");
				}
			} else {
				error("Procedure " + callee + " called but not declared");
			}
		}
	}
	
	@Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
		checkAssignmentToVar(ctx.lhs);
		return super.visitAssignStmt(ctx);
	}

	@Override
	public Void visitHavocStmt(HavocStmtContext ctx) {
		checkAssignmentToVar(ctx.var);
		return super.visitHavocStmt(ctx);
	}

	private void checkAssignmentToVar(Token receivingNameToken) {
		checkNameInScope(receivingNameToken);
		String receivingName = receivingNameToken.getText();
		if(parameters.contains(receivingName)) {
			error("Attempt to modify parameter " + receivingName + " at line " + receivingNameToken.getLine());
		}
	}
	
	private void error(String errorString) {
		errors.add(errorString);
	}

	public boolean hasErrors() {
		return !errors.isEmpty();
	}

	public Iterable<String> getErrors() {
		return errors;
	}
	
}


                                         