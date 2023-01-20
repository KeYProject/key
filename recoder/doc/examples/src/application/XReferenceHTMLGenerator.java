package application;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import recoder.CrossReferenceServiceConfiguration;
import recoder.abstraction.Constructor;
import recoder.abstraction.Method;
import recoder.abstraction.Package;
import recoder.abstraction.ProgramModelElement;
import recoder.abstraction.Type;
import recoder.abstraction.Variable;
import recoder.convenience.Format;
import recoder.convenience.Naming;
import recoder.io.PropertyNames;
import recoder.java.CompilationUnit;
import recoder.java.Identifier;
import recoder.java.NamedProgramElement;
import recoder.java.NonTerminalProgramElement;
import recoder.java.PrettyPrinter;
import recoder.java.PrettyPrintingException;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.expression.operator.New;
import recoder.java.reference.ConstructorReference;
import recoder.java.reference.FieldReference;
import recoder.java.reference.MethodReference;
import recoder.java.reference.PackageReference;
import recoder.java.reference.SuperConstructorReference;
import recoder.java.reference.ThisConstructorReference;
import recoder.java.reference.TypeReference;
import recoder.java.reference.UncollatedReferenceQualifier;
import recoder.java.reference.VariableReference;
import recoder.kit.UnitKit;
import recoder.service.SourceInfo;
import recoder.util.ObjectIDAssignment;
import recoder.util.Order;
import recoder.util.Sorting;

/**
 * @author AL
 */
public class XReferenceHTMLGenerator extends PrettyPrinter {

    public static void main(String[] args) throws IOException {
        CrossReferenceServiceConfiguration sc = new CrossReferenceServiceConfiguration();
        RecoderProgram.setup(sc, XReferenceHTMLGenerator.class, args);
        List<CompilationUnit> units = sc.getSourceFileRepository().getCompilationUnits();
        System.out.println("Generating HTML Source Views...");
        XReferenceHTMLGenerator hpp = new XReferenceHTMLGenerator(sc, new PrintWriter(System.out));
        hpp.printHTMLReferenceFiles(units);
    }

    private CrossReferenceServiceConfiguration serviceConfiguration;

    private SourceInfo sourceInfo; // cached

    private Writer refWriter;

    private String outputPath;

    private Set referredEntities;

    private ObjectIDAssignment cuIDs = new ObjectIDAssignment();

    public XReferenceHTMLGenerator(CrossReferenceServiceConfiguration sc, Writer out) {
        super(out, sc.getProjectSettings().getProperties());
        this.serviceConfiguration = sc;
        sourceInfo = sc.getSourceInfo();
        outputPath = sc.getProjectSettings().getProperty(PropertyNames.OUTPUT_PATH);
        File outputDir = new File(outputPath);
        if (!outputDir.exists()) {
            outputDir.mkdirs();
        }
        referredEntities = new HashSet();
    }

    public void visitIdentifier(Identifier x) {
        printHeader(x);
        printElementIndentation(x);
        NonTerminalProgramElement npe = x.getParent();
        if (npe instanceof Reference) {
            if (npe instanceof UncollatedReferenceQualifier) {
                npe = (NamedProgramElement) sourceInfo.resolveURQ((UncollatedReferenceQualifier) npe);
            }
            if (npe instanceof TypeReference) {
                Type pme = sourceInfo.getType((TypeReference) npe);
                if (pme != null) {
                    printReference(x, pme);
                    return;
                }
                // void type fall through
            } else if (npe instanceof VariableReference) {
                Variable pme = sourceInfo.getVariable((VariableReference) npe);
                printReference(x, pme);
                return;
            } else if (npe instanceof ConstructorReference) {
                Constructor pme = sourceInfo.getConstructor((ConstructorReference) npe);
                printReference(x, pme);
                return;
            } else if (npe instanceof MethodReference) {
                Method pme = sourceInfo.getMethod((MethodReference) npe);
                printReference(x, pme);
                return;
            } else if (npe instanceof PackageReference) {
                Package pme = sourceInfo.getPackage((PackageReference) npe);
                printReference(x, pme);
                return;
            }
        } else if (npe instanceof ProgramModelElement) {
            super.print("<U>");
            printAnchorStart(npe);
            super.print(x.getText());
            super.print("</A></U>");
            printFooter(x);
            return;
        }
        super.print(x.getText());
        printFooter(x);
    }

    private void printReference(Identifier x, ProgramModelElement pme) {
        NonTerminalProgramElement pe = x.getParent();
        printLink(pe, pme);
        String name = x.getText();
        super.print(name);
        super.print("</A>");
        printFooter(x);
    }

    public void print(String str) {
        for (int i = 0, len = str.length(); i < len; i += 1) {
            char c = str.charAt(i);
            switch (c) {
            case 'ä':
                super.print("&auml;");
                break;
            case '<':
                super.print("&lt;");
                break;
            case '&':
                super.print("&amp;");
                break;
            case '>':
                super.print("&gt;");
                break;
            default:
                super.print(c);
                break;
            }
        }
    }

    public void visitNew(New x) {
        printHeader(x);
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            print('(');
        }
        if (x.getReferencePrefix() != null) {
            printElement(0, x.getReferencePrefix());
            print('.');
        }
        printElementIndentation(x);
        if (x.getClassDeclaration() == null) {
            printLink(x, sourceInfo.getConstructor(x));
        }
        print("new");
        if (x.getClassDeclaration() == null) {
            super.print("</A>");
        }
        printElement(1, x.getTypeReference());
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print("(");
        } else {
            print(" (");
        }
        if (x.getArguments() != null) {
            printCommaList(x.getArguments());
        }
        print(')');
        if (x.getClassDeclaration() != null) {
            printElement(1, x.getClassDeclaration());
        }
        if (addParentheses) {
            print(')');
        }
        if (x.getStatementContainer() != null) {
            print(';');
        }
        printFooter(x);
    }

    public void visitThisConstructorReference(ThisConstructorReference x) {
        printHeader(x);
        printElementIndentation(x);
        printLink(x, sourceInfo.getConstructor(x));
        print("this");
        super.print("</A>");
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print("(");
        } else {
            print(" (");
        }
        if (x.getArguments() != null) {
            printCommaList(x.getArguments());
        }
        print(");");
        printFooter(x);
    }

    public void visitSuperConstructorReference(SuperConstructorReference x) {
        printHeader(x);
        printElementIndentation(x);
        if (x.getReferencePrefix() != null) {
            printElement(x.getReferencePrefix());
            print('.');
        }
        printLink(x, sourceInfo.getConstructor(x));
        print("super");
        super.print("</A>");
        if (getBooleanProperty(GLUE_PARAMETER_LISTS)) {
            print("(");
        } else {
            print(" (");
        }
        if (x.getArguments() != null) {
            printCommaList(0, 0, 0, x.getArguments());
        }
        print(");");
        printFooter(x);
    }

    private void printAnchorStart(ProgramElement pe) {
        super.print("<A NAME=\"" + getIdString(pe) + "\">");
    }

    private void printLink(ProgramElement pe, ProgramModelElement pme) {
        super.print("<A HREF=\"" + HTML_REFFILENAME + "#" + getIdString(pme) + "\">");
        if (!referredEntities.add(pme)) {
            StringBuffer out = new StringBuffer();
            out.append("<HR><A NAME=\"");
            out.append(getIdString(pme));
            out.append("\">");
            if (pe instanceof PackageReference) {
                out.append("Package");
            } else if (pe instanceof TypeReference) {
                out.append("Type");
            } else if (pe instanceof FieldReference) {
                out.append("Field");
            } else if (pe instanceof VariableReference) {
                out.append("Variable");
            } else if (pe instanceof ConstructorReference) {
                out.append("Constructor");
            } else if (pe instanceof MethodReference) {
                out.append("Method");
            }
            out.append("</A> <I>");
            if (pme instanceof ProgramElement) {
                out.append("<A HREF=\"");
                out.append(toHTMLSrcFilename(UnitKit.getCompilationUnit((ProgramElement) pme)));
                out.append('#');
                out.append(getIdString((ProgramElement) pme));
                out.append("\">");
                out.append(Format.toString("%N", pme));
                out.append("</A>");
            } else {
                out.append(Format.toString("%N", pme));
            }
            out.append("</I>\n");
            try {
                refWriter.write(out.toString());
            } catch (IOException ioe) {
                throw new PrettyPrintingException(ioe);
            }
        }
    }

    private String getIdString(Object o) {
        return Long.toString(cuIDs.getID(o), 36);
    }

    private String toHTMLSrcFilename(CompilationUnit cu) {
        return getIdString(cu) + ".html";
    }

    private final static String HTML_REFFILENAME = "XRef.html";

    public void printHTMLReferenceFiles(List<CompilationUnit> cus) throws IOException {
        refWriter = new FileWriter(new File(outputPath, HTML_REFFILENAME));
        refWriter
                .write("<HTML><HEAD><TITLE>References</TITLE><BASE TARGET=\"srcframe\"></HEAD><BODY BGCOLOR=\"#F0F0F0\">\n");
        String[] ulinks = new String[cus.size()];
        for (int i = 0, s = cus.size(); i < s; i += 1) {
            CompilationUnit cu = cus.get(i);
            String cuname = Naming.toCanonicalName(cu);
            String srcfilename = toHTMLSrcFilename(cu);
            ulinks[i] = cuname + " " + srcfilename;

            FileWriter srcWriter = new FileWriter(new File(outputPath, srcfilename));
            srcWriter.write("<HTML><HEAD><TITLE>" + cuname
                    + "</TITLE><BASE TARGET=\"refframe\"></HEAD><BODY BGCOLOR=\"#FFFFFF\"><PRE>\n");
            setWriter(srcWriter);
            visitCompilationUnit(cu);
            srcWriter.write("</PRE></BODY></HTML>\n");
            getWriter().close();
        }
        refWriter.write("</BODY></HTML>\n");
        refWriter.close();
        FileWriter idxWriter = new FileWriter(new File(outputPath, "reference-index.html"));
        idxWriter
                .write("<HTML><HEAD><TITLE>Index</TITLE><BASE TARGET=\"srcframe\"></HEAD><BODY BGCOLOR=\"#FFFFFF\">\n<H1>Primary Unit Classes</H1>\n");

        Sorting.quickSort(ulinks, Order.LEXICAL);
        for (int i = 0; i < ulinks.length; i += 1) {
            String ulink = ulinks[i];
            int sep = ulink.indexOf(' ');
            idxWriter.write("<A HREF=\"" + ulink.substring(sep + 1) + "\">" + ulink.substring(0, sep) + "</A><BR>\n");
        }
        idxWriter.write("</BODY></HTML>\n");
        idxWriter.close();
        FileWriter w = new FileWriter(new File(outputPath, "index.html"));
        w.write("<HTML><HEAD><TITLE>Reference Index</TITLE></HEAD>\n" + "<FRAMESET cols=\"25%,*\">\n"
                + " <FRAME src=\"reference-index.html\" name=\"idxframe\">\n" + " <FRAMESET rows=\"*,50\">\n"
                + "  <FRAME src=\"reference-blank.html\" name=\"srcframe\">\n"
                + "  <FRAME src=\"reference-blank.html\" name=\"refframe\">\n" + " </FRAMESET>\n" + "</FRAMESET>\n"
                + "<NOFRAMES>This document requires frames.</NOFRAMES></HTML>\n");
        w.close();
        w = new FileWriter(new File(outputPath, "reference-blank.html"));
        w.write("<HTML><BODY></BODY></HTML>\n");
        w.close();
    }
}

