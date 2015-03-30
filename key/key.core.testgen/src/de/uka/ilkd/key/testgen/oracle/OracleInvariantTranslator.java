package de.uka.ilkd.key.testgen.oracle;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.RepresentsAxiom;

public class OracleInvariantTranslator {

	private Services services;
	
	public OracleInvariantTranslator(Services services){
		this.services = services;
	}

	public Term getInvariantTerm(Sort s){
		JavaInfo info = services.getJavaInfo();
		TermBuilder tb = new TermBuilder(services.getTermFactory(), services);
		SpecificationRepository spec = services.getSpecificationRepository();

		Sort heapSort = services.getTypeConverter().getHeapLDT().targetSort();

		LogicVariable h = new LogicVariable(new Name("h"), heapSort);


		KeYJavaType kjt = info.getKeYJavaType(s);

		if(!(kjt.getJavaType() instanceof ClassDeclaration 
				|| kjt.getJavaType() instanceof InterfaceDeclaration || kjt.getJavaType() instanceof ArrayDeclaration) 
				)  {
			return tb.tt();
		}

		LogicVariable o = new LogicVariable(new Name("o"), kjt.getSort());
		
		Term result = tb.tt();
		
		for(ClassAxiom c : spec.getClassAxioms(kjt)){

			if(c instanceof RepresentsAxiom && c.getKJT().equals(kjt)){
				RepresentsAxiom ra = (RepresentsAxiom) c;
				
				 Term t = ra.getAxiom(h, o, services);
				 
				 if(t.op().equals(Equality.EQV)){
					 
					 Term[] heaps = new Term[1];
                     heaps[0] = tb.var(h);

                     Term inv = tb.inv(heaps, tb.var(o));
                     Term left = t.sub(0);
                     Term right = t.sub(1);
                     
                     if(left.op().name().equals(inv.op().name())){
                    	 if(!right.equals(tb.tt())){
                    		 result = tb.and(result, right);
                    	 }
                     }
                     else if(right.op().name().equals(inv.op().name())){
                    	 if(!left.op().equals(tb.tt())){
                    		 result = tb.and(result, left);
                    	 }
                     }
					 
					 
				 }


			}

		}

		return tb.tt();





	}

}
