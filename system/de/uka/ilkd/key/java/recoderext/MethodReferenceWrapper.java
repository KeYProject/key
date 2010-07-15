package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.list.generic.ASTList;

public class MethodReferenceWrapper extends MethodReference {

    
    public MethodReferenceWrapper(ReferencePrefix accessPath, Identifier name, 
            ASTList<Expression> args, ASTList<TypeArgumentDeclaration> typeArgs){
        super(accessPath, name, args, typeArgs);
    }
    
    public MethodReferenceWrapper(ReferencePrefix accessPath, Identifier name, 
            ASTList<Expression> args){
        super(accessPath, name, args);  
    }
    
    public MethodReferenceWrapper(ReferencePrefix accessPath, Identifier name){
        super(accessPath, name);
    }
    
    public MethodReferenceWrapper(MethodReference proto){
        super(proto);
    }
    
    public MethodReferenceWrapper deepClone(){
        return new MethodReferenceWrapper(super.deepClone());
    }
        
}
