package tool;
import parser.SimpleCParser.ProcedureDeclContext;

public class VCGenerator {

	private ProcedureDeclContext proc;
	
	public VCGenerator(ProcedureDeclContext proc) {
		this.proc = proc;
		// TODO: You will probably find it useful to add more fields and constructor arguments
	}
	
	public StringBuilder generateVC() {
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
		// TODO: generate the meat of the VC
		
		result.append("\n(check-sat)\n");
		return result;
	}

}
