package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Variable;
import recoder.java.ProgramElement;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ThisReference;
import recoder.kit.ProblemReport;
import recoder.list.CompilationUnitMutableList;
import recoder.list.VariableReferenceList;
import recoder.service.CrossReferenceSourceInfo;


public class LocalClassTransformation extends RecoderModelTransformer {
    
    
    public LocalClassTransformation
        (CrossReferenceServiceConfiguration services, 
                CompilationUnitMutableList units) {    
        super(services, units);
    }
    
    public ProblemReport analyze() {
         HashSet cds = classDeclarations();
         Iterator it = cds.iterator();
         while(it.hasNext()){
             ClassDeclaration cd = (ClassDeclaration) it.next();
             (new FinalOuterVarsCollector()).walk(cd);
         }     
         return super.analyze();
    }
    
    protected void makeExplicit(TypeDeclaration td) {
        LinkedList outerVars = (LinkedList) localClass2finalVar.get(td);
        CrossReferenceSourceInfo si = services.getCrossReferenceSourceInfo();
        if(outerVars!=null){
            for(int i=0; i<outerVars.size(); i++){
                Variable v = (Variable) outerVars.get(i);
                VariableReferenceList refs = si.getReferences(v);
                for(int j=0; j<refs.size(); j++){
                    if(si.getContainingClassType(refs.getVariableReference(j)) !=
                        si.getContainingClassType((ProgramElement) v)){
                        refs.getVariableReference(j).getASTParent().replaceChild(
                                refs.getVariableReference(j), new FieldReference(new ThisReference(), 
                                        new ImplicitIdentifier(ImplicitFieldAdder.FINAL_VAR_PREFIX+
                                                v.getName())));
                        td.makeAllParentRolesValid();
                    }
                }
            }
        }
    }
}
