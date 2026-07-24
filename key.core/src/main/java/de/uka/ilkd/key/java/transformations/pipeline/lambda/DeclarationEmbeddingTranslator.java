import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.util.Context;
import com.sun.tools.javac.util.List;
import org.jmlspecs.openjml.JmlTree;
import org.jmlspecs.openjml.JmlTreeTranslator;

public class DeclarationEmbeddingTranslator extends JmlTreeTranslator {
    private final JmlTree.Maker maker;
    private final java.util.List<? extends JCTree> embeddable;

    public DeclarationEmbeddingTranslator(Context context, java.util.List<? extends JCTree> embeddable) {
        maker = JmlTree.Maker.instance(context);
        this.embeddable = embeddable;
    }

    @Override
    public JCTree translate(JCTree tree) {
        if (tree instanceof JCTree.JCClassDecl) {
            JCTree.JCClassDecl classDecl = (JCTree.JCClassDecl) tree;
            List<JCTree> newDefs = classDecl.defs.appendList(List.from(embeddable));
            return maker.ClassDef(classDecl.mods, classDecl.name, classDecl.typarams, classDecl.extending, classDecl.implementing, newDefs);
        }
        return super.translate(tree);
    }
}
