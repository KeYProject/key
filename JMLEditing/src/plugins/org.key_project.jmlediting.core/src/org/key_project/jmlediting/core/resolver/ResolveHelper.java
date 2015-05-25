package org.key_project.jmlediting.core.resolver;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class ResolveHelper extends ASTVisitor {

    private List<IASTNode> IASTList = new ArrayList<IASTNode>();
    private List<IASTNode> unresolvedList = new ArrayList<IASTNode>();
    //private ResolveResult result = null;
       
    
    public ResolveHelper(List<IASTNode> iASTList) {
        // Take and save the JMLAST
        IASTList.addAll(iASTList);
        // Get all the unresolved Strings.. still has operators.
        unresolvedList.addAll(Nodes.getAllNodesOfType(iASTList.get(0), NodeTypes.STRING));
        // TODO: maybe get an Operator Profile, to parse them.. since we need this for later things.
        // TODO: I will ignore this for now, though.
    }

    @Override
    public boolean visit(TypeDeclaration node) {
        System.out.println("TypeDeclaration: " + node.getName());
        
        ITypeBinding binding = node.resolveBinding();
        
        if(binding != null) binding.getDeclaredFields();
        
        
        //for(IASTNode s : unresolvedList) {
        //    if() // TODO
        //}
        
        
        return super.visit(node);
    }
    
    @Override
    public boolean visit(MethodDeclaration node) {
        System.out.println("MethodDeclaration: " + node.getName());
        
        IMethodBinding binding = node.resolveBinding();
        if(binding != null) binding.getName();
        
        return super.visit(node);
    }
    
    // Field Declaration .. we have to save this ... they are referenced in type binding.
    @Override
    public boolean visit(VariableDeclarationFragment node) {
        System.out.println("VariableDeclarationFragment: " + node.getName());
        return super.visit(node);
    }
    
    @Override
    public boolean visit(SingleVariableDeclaration node) {
        System.out.println("SingleVariableDeclaration: " + node.getName());
        
        IVariableBinding binding = node.resolveBinding();
        if(binding != null) binding.getName();
        
        return super.visit(node);
    }
}
