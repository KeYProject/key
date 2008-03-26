package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import de.uka.ilkd.key.java.recoderext.RecoderModelTransformer.TransformerCache;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Variable;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.declaration.ClassDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.reference.FieldReference;
import recoder.java.reference.ThisReference;
import recoder.java.reference.VariableReference;
import recoder.kit.ProblemReport;
import recoder.service.CrossReferenceSourceInfo;


public class LocalClassTransformation extends RecoderModelTransformer {
    
    
    public LocalClassTransformation(
            CrossReferenceServiceConfiguration services, TransformerCache cache) {
        super(services, cache);
    }

    public ProblemReport analyze() {
         Set cds = classDeclarations();
         Iterator it = cds.iterator();
         while(it.hasNext()){
             ClassDeclaration cd = (ClassDeclaration) it.next();
             if(cd.getName()==null || cd.getStatementContainer() !=null){
                 (new FinalOuterVarsCollector()).walk(cd);
             }
         }     
         return super.analyze();
    }
    
    protected void makeExplicit(TypeDeclaration td) {
        LinkedList outerVars = (LinkedList) getLocalClass2FinalVar().get(td);
        CrossReferenceSourceInfo si = services.getCrossReferenceSourceInfo();
        if(outerVars!=null){
            for(int i=0; i<outerVars.size(); i++){
                Variable v = (Variable) outerVars.get(i);
                List<VariableReference> refs = si.getReferences(v);
                for(int j=0; j<refs.size(); j++){
                    if(si.getContainingClassType(refs.get(j)) !=
                        si.getContainingClassType((ProgramElement) v)){
                        refs.get(j).getASTParent().replaceChild(
                                refs.get(j), new FieldReference(new ThisReference(), 
                                        new ImplicitIdentifier(ImplicitFieldAdder.FINAL_VAR_PREFIX+
                                                v.getName())));
                        td.makeAllParentRolesValid();
                    }
                }
            }
        }
    }
}
