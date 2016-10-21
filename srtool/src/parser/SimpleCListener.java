// Generated from SimpleC.g by ANTLR 4.5.3
package parser;
import org.antlr.v4.runtime.tree.ParseTreeListener;

/**
 * This interface defines a complete listener for a parse tree produced by
 * {@link SimpleCParser}.
 */
public interface SimpleCListener extends ParseTreeListener {
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#program}.
	 * @param ctx the parse tree
	 */
	void enterProgram(SimpleCParser.ProgramContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#program}.
	 * @param ctx the parse tree
	 */
	void exitProgram(SimpleCParser.ProgramContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#varDecl}.
	 * @param ctx the parse tree
	 */
	void enterVarDecl(SimpleCParser.VarDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#varDecl}.
	 * @param ctx the parse tree
	 */
	void exitVarDecl(SimpleCParser.VarDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#procedureDecl}.
	 * @param ctx the parse tree
	 */
	void enterProcedureDecl(SimpleCParser.ProcedureDeclContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#procedureDecl}.
	 * @param ctx the parse tree
	 */
	void exitProcedureDecl(SimpleCParser.ProcedureDeclContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#formalParam}.
	 * @param ctx the parse tree
	 */
	void enterFormalParam(SimpleCParser.FormalParamContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#formalParam}.
	 * @param ctx the parse tree
	 */
	void exitFormalParam(SimpleCParser.FormalParamContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#prepost}.
	 * @param ctx the parse tree
	 */
	void enterPrepost(SimpleCParser.PrepostContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#prepost}.
	 * @param ctx the parse tree
	 */
	void exitPrepost(SimpleCParser.PrepostContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#requires}.
	 * @param ctx the parse tree
	 */
	void enterRequires(SimpleCParser.RequiresContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#requires}.
	 * @param ctx the parse tree
	 */
	void exitRequires(SimpleCParser.RequiresContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#ensures}.
	 * @param ctx the parse tree
	 */
	void enterEnsures(SimpleCParser.EnsuresContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#ensures}.
	 * @param ctx the parse tree
	 */
	void exitEnsures(SimpleCParser.EnsuresContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#stmt}.
	 * @param ctx the parse tree
	 */
	void enterStmt(SimpleCParser.StmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#stmt}.
	 * @param ctx the parse tree
	 */
	void exitStmt(SimpleCParser.StmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssignStmt(SimpleCParser.AssignStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#assignStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssignStmt(SimpleCParser.AssignStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#assertStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssertStmt(SimpleCParser.AssertStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#assertStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssertStmt(SimpleCParser.AssertStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void enterAssumeStmt(SimpleCParser.AssumeStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#assumeStmt}.
	 * @param ctx the parse tree
	 */
	void exitAssumeStmt(SimpleCParser.AssumeStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void enterHavocStmt(SimpleCParser.HavocStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#havocStmt}.
	 * @param ctx the parse tree
	 */
	void exitHavocStmt(SimpleCParser.HavocStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#callStmt}.
	 * @param ctx the parse tree
	 */
	void enterCallStmt(SimpleCParser.CallStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#callStmt}.
	 * @param ctx the parse tree
	 */
	void exitCallStmt(SimpleCParser.CallStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#ifStmt}.
	 * @param ctx the parse tree
	 */
	void enterIfStmt(SimpleCParser.IfStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#ifStmt}.
	 * @param ctx the parse tree
	 */
	void exitIfStmt(SimpleCParser.IfStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#whileStmt}.
	 * @param ctx the parse tree
	 */
	void enterWhileStmt(SimpleCParser.WhileStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#whileStmt}.
	 * @param ctx the parse tree
	 */
	void exitWhileStmt(SimpleCParser.WhileStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#blockStmt}.
	 * @param ctx the parse tree
	 */
	void enterBlockStmt(SimpleCParser.BlockStmtContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#blockStmt}.
	 * @param ctx the parse tree
	 */
	void exitBlockStmt(SimpleCParser.BlockStmtContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#loopInvariant}.
	 * @param ctx the parse tree
	 */
	void enterLoopInvariant(SimpleCParser.LoopInvariantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#loopInvariant}.
	 * @param ctx the parse tree
	 */
	void exitLoopInvariant(SimpleCParser.LoopInvariantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#invariant}.
	 * @param ctx the parse tree
	 */
	void enterInvariant(SimpleCParser.InvariantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#invariant}.
	 * @param ctx the parse tree
	 */
	void exitInvariant(SimpleCParser.InvariantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#candidateInvariant}.
	 * @param ctx the parse tree
	 */
	void enterCandidateInvariant(SimpleCParser.CandidateInvariantContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#candidateInvariant}.
	 * @param ctx the parse tree
	 */
	void exitCandidateInvariant(SimpleCParser.CandidateInvariantContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#expr}.
	 * @param ctx the parse tree
	 */
	void enterExpr(SimpleCParser.ExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#expr}.
	 * @param ctx the parse tree
	 */
	void exitExpr(SimpleCParser.ExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#ternExpr}.
	 * @param ctx the parse tree
	 */
	void enterTernExpr(SimpleCParser.TernExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#ternExpr}.
	 * @param ctx the parse tree
	 */
	void exitTernExpr(SimpleCParser.TernExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#lorExpr}.
	 * @param ctx the parse tree
	 */
	void enterLorExpr(SimpleCParser.LorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#lorExpr}.
	 * @param ctx the parse tree
	 */
	void exitLorExpr(SimpleCParser.LorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#landExpr}.
	 * @param ctx the parse tree
	 */
	void enterLandExpr(SimpleCParser.LandExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#landExpr}.
	 * @param ctx the parse tree
	 */
	void exitLandExpr(SimpleCParser.LandExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#borExpr}.
	 * @param ctx the parse tree
	 */
	void enterBorExpr(SimpleCParser.BorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#borExpr}.
	 * @param ctx the parse tree
	 */
	void exitBorExpr(SimpleCParser.BorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#bxorExpr}.
	 * @param ctx the parse tree
	 */
	void enterBxorExpr(SimpleCParser.BxorExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#bxorExpr}.
	 * @param ctx the parse tree
	 */
	void exitBxorExpr(SimpleCParser.BxorExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#bandExpr}.
	 * @param ctx the parse tree
	 */
	void enterBandExpr(SimpleCParser.BandExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#bandExpr}.
	 * @param ctx the parse tree
	 */
	void exitBandExpr(SimpleCParser.BandExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void enterEqualityExpr(SimpleCParser.EqualityExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#equalityExpr}.
	 * @param ctx the parse tree
	 */
	void exitEqualityExpr(SimpleCParser.EqualityExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#relExpr}.
	 * @param ctx the parse tree
	 */
	void enterRelExpr(SimpleCParser.RelExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#relExpr}.
	 * @param ctx the parse tree
	 */
	void exitRelExpr(SimpleCParser.RelExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#shiftExpr}.
	 * @param ctx the parse tree
	 */
	void enterShiftExpr(SimpleCParser.ShiftExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#shiftExpr}.
	 * @param ctx the parse tree
	 */
	void exitShiftExpr(SimpleCParser.ShiftExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#addExpr}.
	 * @param ctx the parse tree
	 */
	void enterAddExpr(SimpleCParser.AddExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#addExpr}.
	 * @param ctx the parse tree
	 */
	void exitAddExpr(SimpleCParser.AddExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#mulExpr}.
	 * @param ctx the parse tree
	 */
	void enterMulExpr(SimpleCParser.MulExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#mulExpr}.
	 * @param ctx the parse tree
	 */
	void exitMulExpr(SimpleCParser.MulExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#unaryExpr}.
	 * @param ctx the parse tree
	 */
	void enterUnaryExpr(SimpleCParser.UnaryExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#unaryExpr}.
	 * @param ctx the parse tree
	 */
	void exitUnaryExpr(SimpleCParser.UnaryExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#atomExpr}.
	 * @param ctx the parse tree
	 */
	void enterAtomExpr(SimpleCParser.AtomExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#atomExpr}.
	 * @param ctx the parse tree
	 */
	void exitAtomExpr(SimpleCParser.AtomExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#numberExpr}.
	 * @param ctx the parse tree
	 */
	void enterNumberExpr(SimpleCParser.NumberExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#numberExpr}.
	 * @param ctx the parse tree
	 */
	void exitNumberExpr(SimpleCParser.NumberExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#varrefExpr}.
	 * @param ctx the parse tree
	 */
	void enterVarrefExpr(SimpleCParser.VarrefExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#varrefExpr}.
	 * @param ctx the parse tree
	 */
	void exitVarrefExpr(SimpleCParser.VarrefExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void enterParenExpr(SimpleCParser.ParenExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#parenExpr}.
	 * @param ctx the parse tree
	 */
	void exitParenExpr(SimpleCParser.ParenExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#resultExpr}.
	 * @param ctx the parse tree
	 */
	void enterResultExpr(SimpleCParser.ResultExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#resultExpr}.
	 * @param ctx the parse tree
	 */
	void exitResultExpr(SimpleCParser.ResultExprContext ctx);
	/**
	 * Enter a parse tree produced by {@link SimpleCParser#oldExpr}.
	 * @param ctx the parse tree
	 */
	void enterOldExpr(SimpleCParser.OldExprContext ctx);
	/**
	 * Exit a parse tree produced by {@link SimpleCParser#oldExpr}.
	 * @param ctx the parse tree
	 */
	void exitOldExpr(SimpleCParser.OldExprContext ctx);
}