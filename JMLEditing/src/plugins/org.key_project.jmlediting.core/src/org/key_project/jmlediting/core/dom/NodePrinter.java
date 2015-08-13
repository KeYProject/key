package org.key_project.jmlediting.core.dom;

public class NodePrinter /*implements INodePrinter*/ {
     
   private NodePrinter() {} 
   
   public static String print(final IASTNode node) {
       return node.traverse(new INodeTraverser<StringBuilder>() {

         @Override
         public StringBuilder traverse(IASTNode node, StringBuilder existing) {
            if (node.getType() == NodeTypes.KEYWORD) {
               existing.append(((IKeywordNode)node).getKeywordInstance()).append(" ");
            } else if (node.getType() == NodeTypes.STRING /*|| node.getType() == NodeTypes.SEQ*/) {
               existing.append(node.prettyPrintAST().replaceAll("^\"", "").replaceAll("\"$", "")).append(" ");
            }
            return existing;
         }
          
      }, new StringBuilder()).toString();
   }
}
