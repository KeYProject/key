package de.uka.ilkd.key.java.recoderext;

import recoder.java.Expression;
import recoder.java.Identifier;
import recoder.java.declaration.TypeArgumentDeclaration;
import recoder.java.reference.MethodReference;
import recoder.java.reference.ReferencePrefix;
import recoder.list.generic.ASTList;

public class MethodReferenceWrapper extends MethodReference {

    private Identifier scope;
    
    public MethodReferenceWrapper(ReferencePrefix accessPath, Identifier name, 
            ASTList<Expression> args, ASTList<TypeArgumentDeclaration> typeArgs, Identifier scope){
        super(accessPath, name, args, typeArgs);
        this.scope = scope;
    }
    
    public MethodReferenceWrapper(ReferencePrefix accessPath, Identifier name, 
            ASTList<Expression> args, Identifier scope){
        super(accessPath, name, args);
        this.scope = scope;
    }
    
    public MethodReferenceWrapper(ReferencePrefix accessPath, Identifier name, 
            Identifier scope){
        super(accessPath, name);
        this.scope = scope;
    }
    
    public MethodReferenceWrapper(MethodReference proto, Identifier scope){
        super(proto);
        this.scope = scope;
    }
    
    public MethodReferenceWrapper deepClone(){
        return new MethodReferenceWrapper(super.deepClone(), scope==null ? null : scope.deepClone());
    }
    
    public Identifier getScope(){
        return scope;
    }
    
}
