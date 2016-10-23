package tool;
import parser.GlobalVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.TestVisitor;

public class VCGenerator {

	private ProcedureDeclContext proc;
	private ProgramContext prog;
	private TestVisitor tv = new TestVisitor();
	private GlobalVisitor gl = new GlobalVisitor();
	private StringBuilder result = new StringBuilder("(set-logic QF_LIA)\n");
	
	public VCGenerator(ProgramContext prog, ProcedureDeclContext proc) {
		this.proc = proc;
		this.prog = prog;
		// TODO: You will probably find it useful to add more fields and constructor arguments
	}
	
	public String generateVCGlobal() {
		gl.visit(prog);
		result.append(gl.getSMT().toString());
		result.append("\n(check-sat)\n");
		return result.toString();
		
	}
	
	public StringBuilder generateVC() {
//		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
//		result.append("(set-option :produce-models true)\n");
//		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
//		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
		tv.visit(proc);
		result.append(tv.getSMT());
		
		// TODO: generate the meat of the VC
		
		result.append("\n(check-sat)\n");
		System.out.println(result.toString());
		return result;
	}

}
