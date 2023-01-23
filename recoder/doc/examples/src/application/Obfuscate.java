package application;

import java.util.ArrayList;
import java.util.List;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Method;
import recoder.abstraction.Package;
import recoder.abstraction.ProgramModelElement;
import recoder.convenience.AbstractTreeWalker;
import recoder.convenience.ForestWalker;
import recoder.java.PackageSpecification;
import recoder.java.ProgramElement;
import recoder.java.declaration.ConstructorDeclaration;
import recoder.java.declaration.MethodDeclaration;
import recoder.java.declaration.TypeDeclaration;
import recoder.java.declaration.VariableSpecification;
import recoder.kit.MethodKit;
import recoder.kit.PackageKit;
import recoder.kit.Problem;
import recoder.kit.ProblemReport;
import recoder.kit.TwoPassTransformation;
import recoder.kit.transformation.RenameMethod;
import recoder.kit.transformation.RenamePackage;
import recoder.kit.transformation.RenameType;
import recoder.kit.transformation.RenameVariable;

public class Obfuscate extends TwoPassTransformation {

    private List<TwoPassTransformation> transformations;

    public Obfuscate(CrossReferenceServiceConfiguration sc) {
        super(sc);
    }

    public static void main(String[] args) {
        RecoderProgram.execute(new Obfuscate(new CrossReferenceServiceConfiguration()), args);
    }

    private boolean mayRename(Method m) {
        List<Method> ml = MethodKit.getRedefinedMethods(m);
        if (!ml.isEmpty()) {
            return false;
        }
        return !MethodKit.isMain(getNameInfo(), m);
    }

    private boolean mayRename(Package p) {
        return PackageKit.getNonSourcePackageTypes(p).isEmpty();
    }

    public ProblemReport analyze() {
        transformations = new ArrayList<TwoPassTransformation>();
        CrossReferenceServiceConfiguration config = getServiceConfiguration();
        ProblemReport report = EQUIVALENCE;
        AbstractTreeWalker tw = new ForestWalker(getSourceFileRepository().getKnownCompilationUnits());
        while (tw.next()) {
            ProgramElement pe = tw.getProgramElement();
            TwoPassTransformation t;
            if (pe instanceof TypeDeclaration) {
                TypeDeclaration td = (TypeDeclaration) pe;
                if (td.getName() != null) {
                    t = new RenameType(config, td, createName(td));
                    report = t.analyze();
                    if (report instanceof Problem) {
                        return setProblemReport(report);
                    }
                    transformations.add(t);
                }
            } else if (pe instanceof VariableSpecification) {
                VariableSpecification vs = (VariableSpecification) pe;
                t = new RenameVariable(config, vs, createName(vs));
                report = t.analyze();
                if (report instanceof Problem) {
                    return setProblemReport(report);
                }
                transformations.add(t);
            } else if (pe instanceof MethodDeclaration) {
                MethodDeclaration md = (MethodDeclaration) pe;
                if (!(pe instanceof ConstructorDeclaration) && mayRename(md)) {
                    t = new RenameMethod(config, md, createName(md));
                    report = t.analyze();
                    if (report instanceof Problem) {
                        return setProblemReport(report);
                    }
                    transformations.add(t);
                }
            } else if (pe instanceof PackageSpecification) {
                Package pkg = getSourceInfo().getPackage(((PackageSpecification) pe).getPackageReference());
                if (mayRename(pkg)) {
                    t = new RenamePackage(config, pkg, createName(pkg));
                    report = t.analyze();
                    if (report instanceof Problem) {
                        return setProblemReport(report);
                    }
                    transformations.add(t);
                }
            }
        }
        return setProblemReport(EQUIVALENCE);
    }

    public void transform() {
        super.transform();
        for (int i = 0, s = transformations.size(); i < s; i += 1) {
            transformations.get(i).transform();
        }
    }

    private static long count = 0;

    private static String createName(ProgramModelElement pme) {
        /*
         * We assume that names with a leading '_' are not used in the input
         * program. The renaming transformations will issue an error if a
         * problem is encountered (as of 0.61, this is done for packages only
         * and prepared for methods). For a real world application, in case of a
         * problem originating from a name clash with an existing name, a
         * different name would have to be chosen.
         */
        return "_" + (count++);
    }
}