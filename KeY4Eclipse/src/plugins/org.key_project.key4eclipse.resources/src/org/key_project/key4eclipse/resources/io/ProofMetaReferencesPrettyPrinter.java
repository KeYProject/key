package org.key_project.key4eclipse.resources.io;

import java.io.IOException;
import java.io.Writer;

import org.key_project.util.collection.ImmutableArray;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.While;

/**
 * Extends the {@link PrettyPrinter} in order to print comments for all loop types and inline methods.
 * @author Stefan Käsdorf
 */
public class ProofMetaReferencesPrettyPrinter extends PrettyPrinter {

   public ProofMetaReferencesPrettyPrinter(Writer o, boolean noLineFeed) {
      super(o, noLineFeed);
   }
   
   @Override
   public void printDo(Do x) throws IOException {
      Comment[] comments = x.getComments();
      if(comments != null){
         for(Comment c : comments){
            printComment(c);
         }
      }
      super.printDo(x);
   }
   
   @Override
   public void printFor(For x) throws IOException {
      Comment[] comments = x.getComments();
      if(comments != null){
         for(Comment c : comments){
            printComment(c);
         }
      }
      super.printFor(x);
   }
   
   @Override
   public void printWhile(While x) throws IOException{
      Comment[] comments = x.getComments();
      if(comments != null){
         for(Comment c : comments){
            printComment(c);
         }
      }
      super.printWhile(x);
   }

   public void printInlineMethodDeclaration(MethodDeclaration x) throws IOException {
        printHeader(x);
        int m = 0;
        if (x.getModifiers() != null) {
            ImmutableArray<Modifier> mods = x.getModifiers();
            m = mods.size();
            writeKeywordList(mods);
        }
        if (x.getTypeReference() != null) {
            if (m > 0) {
           writeElement(1, x.getTypeReference());
            } else {
           writeElement(x.getTypeReference());
            }
            writeElement(1, x.getProgramElementName());
        } else if (x.getTypeReference() == null
                && !(x instanceof ConstructorDeclaration)) {
            write(" void ");
            writeElement(1, x.getProgramElementName());
        } else {
            if (m > 0) {
           writeElement(1, x.getProgramElementName());
            } else {
           writeElement(x.getProgramElementName());
            }
        }
        write(" (");
        if (x.getParameters() != null) {
            writeCommaList(1, x.getParameters());
        }
        write(")");
        if (x.getThrown() != null) {
            writeElement(1, x.getThrown());
        }
        if (x.getBody() != null) {
            writeElement(1, x.getBody());
        } else {
            write(";");
        }
        printFooter(x);
   }
   
}
