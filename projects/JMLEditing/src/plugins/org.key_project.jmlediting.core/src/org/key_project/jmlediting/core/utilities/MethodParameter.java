package org.key_project.jmlediting.core.utilities;

import java.util.List;

import org.eclipse.jdt.core.dom.SingleVariableDeclaration;

public class MethodParameter {
   private int startOffset;
   private List<SingleVariableDeclaration> parameters;

   public MethodParameter() {
      super();
   }

   public MethodParameter(final int startOffset,
         final List<SingleVariableDeclaration> parameters) {
      super();
      this.startOffset = startOffset;
      this.parameters = parameters;
   }

   public int getStartOffset() {
      return this.startOffset;
   }

   public void setStartOffset(final int startOffset) {
      this.startOffset = startOffset;
   }

   public List<SingleVariableDeclaration> getParameters() {
      return this.parameters;
   }

   public void setParameters(final List<SingleVariableDeclaration> parameters) {
      this.parameters = parameters;
   }
}
