package application;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.CrossReferenceServiceConfiguration;
import recoder.ParserException;
import recoder.ProgramFactory;
import recoder.abstraction.Method;
import recoder.convenience.TreeWalker;
import recoder.java.CompilationUnit;
import recoder.java.ProgramElement;
import recoder.java.expression.literal.StringLiteral;
import recoder.java.reference.MethodReference;
import recoder.kit.MiscKit;
import recoder.kit.Problem;
import recoder.kit.ProblemReport;
import recoder.kit.Transformation;
import recoder.kit.TwoPassTransformation;
import recoder.kit.transformation.PrependExpressionWithStatements;
import recoder.service.SourceInfo;

/**
 * @author AL
 */
public class Instrumentalize extends Transformation {

    public Instrumentalize(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    public static void main(String[] args) {
        RecoderProgram.execute(new Instrumentalize(new CrossReferenceServiceConfiguration()), args);
    }

    public ProblemReport execute() {
        Set inserted = new HashSet();
        CrossReferenceServiceConfiguration config = getServiceConfiguration();
        ProgramFactory pf = getProgramFactory();
        SourceInfo si = getSourceInfo();
        List<CompilationUnit> units = getSourceFileRepository().getKnownCompilationUnits();
        for (int i = 0; i < units.size(); i += 1, inserted.clear()) {
            CompilationUnit cu = units.get(i);
            TreeWalker tw = new TreeWalker(cu);
            while (tw.next()) {
                ProgramElement pe = tw.getProgramElement();
                if (pe instanceof MethodReference) {
                    if (inserted.contains(pe)) {
                        TreeWalker ttw = new TreeWalker(pe);
                        ttw.next();
                        while (ttw.next()) {
                            tw.next();
                        }
                        continue;
                    }
                    MethodReference caller = (MethodReference) pe;
                    MethodReference insert = null;
                    try {
                        insert = (MethodReference) pf.parseExpression("System.out.println(\"\")");
                    } catch (ParserException e) {
                    }
                    StringLiteral text = (StringLiteral) insert.getArguments().get(0);
                    // setText is okay to call for an invisible element!
                    Method callee = si.getMethod(caller);
                    text.setValue("\"Call to " + callee.getFullName() + " from "
                            + MiscKit.getParentTypeDeclaration(pe).getFullName() + "\"");
                    insert.makeAllParentRolesValid();
                    MiscKit.unindent(insert);
                    TwoPassTransformation t = new PrependExpressionWithStatements(config, caller, insert);
                    ProblemReport report = t.analyze();
                    if (report instanceof Problem) {
                        return setProblemReport(report);
                    }
                    if (report != IDENTITY) {
                        t.transform();
                        inserted.add(insert);
                        tw.reset(cu);
                    }
                }
            }
        }
        return setProblemReport(EQUIVALENCE);
    }

}