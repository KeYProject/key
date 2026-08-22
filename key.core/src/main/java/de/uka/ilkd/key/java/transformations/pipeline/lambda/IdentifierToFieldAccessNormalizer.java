import com.sun.org.apache.bcel.internal.generic.Select;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Name;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeTranslator;

/**
 * Converts all Identifiers, that reference class-fields into field accesses.
 * Example `class Test { int a; void m() {a = 2; }}` will become
 * `class Test { int a; void m() {this.a = 2; }}`
 * Usage: identifierToFieldAccessNormalizer.translate(myAst)
 */
public class IdentifierToFieldAccessNormalizer {
    @Override
    public JCTree translate(JCTree tree) {
        if (tree instanceof JCTree.JCIdent) {
            JCTree.JCIdent ident = (JCTree.JCIdent) tree;
            if (ident.sym != null
                    && ident.sym.owner instanceof Symbol.ClassSymbol
                    && !ident.name.toString().equals("this")
                    && !(ident.type instanceof Type.ClassType)
            ) {
                JCTree.JCFieldAccess select = maker.Select(maker.This(ident.sym.owner.type), ident.name);
                select.sym = ident.sym;
                return select;
            }
        }
        return super.translate(tree);
    }

}
