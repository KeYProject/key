package de.uka.ilkd.key.java.recoderext;

import java.util.*;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Variable;
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
         for (final ClassDeclaration cd : classDeclarations()) {
             if(cd.getName() == null || cd.getStatementContainer() !=null){
                 (new FinalOuterVarsCollector()).walk(cd);
             }
         }     
         return super.analyze();
    }
    
    protected void makeExplicit(TypeDeclaration td) {
        List<Variable> outerVars = getLocalClass2FinalVar().get(td);
        CrossReferenceSourceInfo si = services.getCrossReferenceSourceInfo();
        if(outerVars!=null){
            for (final Variable v : outerVars) {
                for (final VariableReference vr : si.getReferences(v)){
                    if (si.getContainingClassType(vr) !=
                        si.getContainingClassType((ProgramElement) v)){
                        vr.getASTParent().replaceChild(
                                vr, new FieldReference(new ThisReference(), 
                                        new ImplicitIdentifier(ImplicitFieldAdder.FINAL_VAR_PREFIX+
                                                v.getName())));
                        td.makeAllParentRolesValid();
                    }
                }
            }
        }
    }
}
