package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.HashMap;
import java.util.LinkedList;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.resolver.ResolveResult;

/**
 * ResolverTask is a container for information, that will be used every time next() is called
 * in the {@link Resolver} class. The information is set during the task building in
 * {@link TaskBuilder#buildResolverTask(IASTNode)}.
 * 
 * @author Christopher Beckmann
 */
public final class ResolverTask {

   private boolean isMethod;
   private boolean isArrayAcess;
   private boolean isKeyword;
   private boolean isClass;
   private boolean isArray;
   private boolean isTypeVariable;
   private int skipIdentifier;
   private String resolveString;
   private IStringNode node;
   private ResolveResult lastResult;
   private ITypeBinding originalTypeBinding;
   private HashMap<String, ITypeBinding> typeArguments;
   private LinkedList<IASTNode> parameters;

   /**
    * Constructor of the Resolver Task. It initializes all the fields of the container to
    * false for all booleans, 0 for the integer {@code skipIdentifier}, empty hash maps and
    * linked lists for {@code typeArguments} and {@code parameters} and null to the rest.
    */
   public ResolverTask() {
      setMethod(false);
      setArrayAcess(false);
      setKeyword(false);
      setClass(false);
      setArray(false);
      setTypeVariable(false);
      setSkipIdentifier(0);
      setResolveString(null);
      setNode(null);
      setLastResult(null);
      setOriginalTypeBinding(null);
      setTypeArguments(new HashMap<String, ITypeBinding>());
      setParameters(new LinkedList<IASTNode>());
   }

   /** Does this task represent a method call?
    * 
    * @return true, if this tasks represents a method call. false if not.
    */
   public final boolean isMethod() {
      return isMethod;
   }

   public final void setMethod(final boolean isMethod) {
      this.isMethod = isMethod;
   }

   public final boolean isArrayAcess() {
      return isArrayAcess;
   }

   public final void setArrayAcess(final boolean isArrayAcess) {
      this.isArrayAcess = isArrayAcess;
   }

   public final boolean isKeyword() {
      return isKeyword;
   }

   public final void setKeyword(final boolean isKeyword) {
      this.isKeyword = isKeyword;
   }

   public final boolean isClass() {
      return isClass;
   }

   public final void setClass(final boolean isClass) {
      this.isClass = isClass;
   }

   public final boolean isArray() {
      return isArray;
   }

   public final void setArray(final boolean isArray) {
      this.isArray = isArray;
   }

   public final boolean isTypeVariable() {
      return isTypeVariable;
   }

   public final void setTypeVariable(final boolean isTypeVariable) {
      this.isTypeVariable = isTypeVariable;
   }

   public final int getSkipIdentifier() {
      return skipIdentifier;
   }

   public final void setSkipIdentifier(final int skipIdentifier) {
      this.skipIdentifier = skipIdentifier;
   }

   public final String getResolveString() {
      return resolveString;
   }

   public final void setResolveString(final String resolveString) {
      this.resolveString = resolveString;
   }

   public final IStringNode getNode() {
      return node;
   }

   public final void setNode(final IStringNode node) {
      this.node = node;
   }

   public final ResolveResult getLastResult() {
      return lastResult;
   }

   public final void setLastResult(final ResolveResult lastResult) {
      this.lastResult = lastResult;
   }

   public final ITypeBinding getOriginalTypeBinding() {
      return originalTypeBinding;
   }

   public final void setOriginalTypeBinding(final ITypeBinding originalTypeBinding) {
      this.originalTypeBinding = originalTypeBinding;
   }

   public final LinkedList<IASTNode> getParameters() {
      return parameters;
   }

   public final void setParameters(final LinkedList<IASTNode> parameters) {
      this.parameters = parameters;
   }

   public HashMap<String, ITypeBinding> getTypeArguments() {
      return typeArguments;
   }

   public void setTypeArguments(final HashMap<String, ITypeBinding> typeArguments) {
      this.typeArguments = typeArguments;
   }

   @Override
   public String toString() {
      final StringBuilder sb = new StringBuilder();
      if (resolveString != null) {
         sb.append(resolveString);
      }
      if (isMethod) {
         sb.append("(");
         for (int i = 0; i < parameters.size(); i++) {
            sb.append("?");
            if (i < parameters.size() - 1) {
               sb.append(" ,");
            }
         }
         sb.append(")");
      }
      if (isArrayAcess) {
         sb.append("[]");
      }
      return sb.toString();
   }

}