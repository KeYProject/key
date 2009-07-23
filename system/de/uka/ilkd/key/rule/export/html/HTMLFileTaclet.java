// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.rule.export.html;

import java.io.IOException;
import java.io.Writer;
import java.util.Iterator;

import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.export.*;

public class HTMLFileTaclet extends HTMLFile {
    
    private ListOfTacletModelInfo tacletInfos;
    
    public HTMLFileTaclet(HTMLModel htmlModel, HTMLContainer htmlContainer, ListOfTacletModelInfo tinfos, int num) {
        super(htmlModel, htmlContainer, "taclets"+num+".html");
        tacletInfos = tinfos;
    }

    protected String getTitle() {
        return "Taclets details";
    }

    protected String getShortTitle() {
        return getTitle();
    }
    
    public void init(RuleExportModel model) {
        super.init(model);
        
        IteratorOfTacletModelInfo it = tacletInfos.iterator();
        while (it.hasNext()) {
            final TacletModelInfo tacletInfo = it.next();
            getFragmentAnchor(tacletInfo);
        }
    }

    protected void write(Writer w) throws IOException {
        StringBuffer out = new StringBuffer();
        
        writeHeader(out);
        
        writeTopAnchor(out);
        
        writeNavBar(out);
        
        writeTacletDetails(out);
        
        writeFooter(out);
        
        w.write(out.toString());
    }

    private void writeTacletDetails ( StringBuffer out ) {
        IteratorOfTacletModelInfo it = tacletInfos.iterator();
        while (it.hasNext()) {
            final TacletModelInfo tacletInfo = it.next();
            writeTacletDetails( out, tacletInfo );
        }
    }

    private void writeTacletDetails ( StringBuffer out, TacletModelInfo tinfo ) {
        final HTMLAnchor anchor = getFragmentAnchor ( tinfo );

        // header
        out.append ( "<!-- rule details -->\n" );
        out.append ( "<div class=\"rule\" id=\"" + anchor + "\">\n<h2>" + tinfo.name ()
                + "</h2>\n" );
        out.append ( "<dl>\n" );

        // display name
        out.append ( "<dt>display name</dt><dd>" );
        writeDisplayNameLink(out, tinfo.getDisplayName() ); 
        out.append ( "</dd>\n" );
        
        // helpstring
        final String helpText = tinfo.getTaclet().helpText();
        if ( helpText != null && !helpText.equals("") )
        {
        	out.append ( "<dt>help text</dt><dd>" );
        	out.append ( helpText );
        	out.append ( "</dd>\n" );
        }
        
        // options
        if ( tinfo.getOptions().size() > 0 ) {
            out.append ( "<dt>options</dt><dd>" );
            writeTacletOptions ( out, tinfo );
            out.append ( "</dd>\n" );
        }

        // kind
        String kind = getRuleKind ( tinfo );
        out.append ( "<dt>kind</dt><dd>" + kind + "</dd>\n" );

        // rule sets
        out.append ( "<dt>contained in</dt><dd>" );
        writeTacletRuleSets ( out, tinfo );
        out.append ( "</dd>\n" );
        
        // introduced by
        final TacletModelInfo introducer = tinfo.getIntroducingTaclet();
        if ( introducer != null) {
            out.append ( "<dt>introduced by</dt><dd>" );
            writeTacletLink ( out, introducer );
            out.append ( "</dd>\n" );
        }
        
        // filename
        out.append ( "<dt>source file</dt><dd>" + tinfo.getFilename()
                + "</dd>\n" );

        // footer
        out.append ( "</dl>\n" );
        out.append ( "</div>\n\n" );
        
        writeTacletDefinition ( out, tinfo );

        writeTopLink ( out );
    }

    private void writeTacletRuleSets ( StringBuffer out, TacletModelInfo t ) {
        final ListOfRuleSetModelInfo ruleSets = t.getRuleSets();
        if (ruleSets.isEmpty ()) {
            out.append ( "none" );
        } else {
            boolean first = true;
            final IteratorOfRuleSetModelInfo it = ruleSets.iterator ();
            while (it.hasNext ()) {
                final RuleSetModelInfo ruleSet = it.next ();
                if (!first) {
                    out.append ( ", " );
                }
                writeRuleSetLink ( out, ruleSet );
                first = false;
            }
        }
    }

    private String getRuleKind ( TacletModelInfo tinfo ) {
        final Taclet t = tinfo.getTaclet ();
        String kind;
        if ( t instanceof NoFindTaclet ) {
            kind = "NoFindTaclet";
        }
        else if ( t instanceof RewriteTaclet ) {
            kind = "RewriteTaclet";
        }
        else if ( t instanceof AntecTaclet ) {
            kind = "AntecTaclet";
        }
        else if ( t instanceof SuccTaclet ) {
            kind = "SuccTaclet";
        }
        else {
            kind = "unknown ("+t.getClass().getName()+")";
        }
        return kind;
    }
    
    private void writeTacletDefinition ( StringBuffer out, TacletModelInfo tinfo ) {
        final Taclet t = tinfo.getTaclet();
        // write schemavariable declarations
        writeTacletSchemaVariables(out, t);
        
        // write pretty-printed taclet definition
        LogicPrinter lp = new LogicPrinter(new ProgramPrinter(), new NotationInfo(), null, true);
        lp.printTaclet(t);
        out.append ( "<pre>\n" );
        appendEscaped ( out, lp.result() );
        out.append ( "</pre>\n" );
    }

    public static void writeTacletSchemaVariables(StringBuffer out, 
                                                  final Taclet t) {
        out.append ( "<pre>\n" );
	writeTacletSchemaVariablesHelper(out, t);
        out.append ( "</pre>\n" );
    }


    public static void writeTacletSchemaVariablesHelper(StringBuffer out, 
                                                        final Taclet t) {
	SetOfSchemaVariable schemaVars = t.getIfFindVariables();
        ListOfNewVarcond lnew = t.varsNew();
	while (!lnew.isEmpty()) {
	    schemaVars = schemaVars.add(lnew.head().getSchemaVariable());
	    lnew = lnew.tail();
	}
	IteratorOfNewDependingOn newDepIt = t.varsNewDependingOn();
	while (newDepIt.hasNext()) {
	    schemaVars = schemaVars.add(newDepIt.next().first());
	}	

        if (schemaVars.size() > 0)
        {
            out.append ( "\\schemaVariables {\n" );
            final IteratorOfSchemaVariable it = schemaVars.iterator();
            while (it.hasNext())
            {
                final SchemaVariable schemaVar = it.next();
                // write indentation
                out.append ( "  " );
                // write declaration
                writeTacletSchemaVariable(out, schemaVar);
                // write newline
                out.append ( ";\n" );
            }
            out.append ( "}\n" );
        }
    }
    
    
    private static void writeSVModifiers(StringBuffer out, SchemaVariable sv) {        
        boolean started = false;        
        if (sv.isRigid() && !(sv instanceof VariableSV)) {
            if (!started) out.append("[");
            out.append("rigid");
            started = true;
        }        
        if (sv instanceof ProgramSV && ((ProgramSV)sv).isListSV()) {
            if (!started) out.append("[");
            else {
                out.append(", ");
            }
            out.append("list");
            started = true;
        }        
        
        if (started) out.append("]");        
    }

    public static void writeTacletSchemaVariable(StringBuffer out, SchemaVariable schemaVar) {
	if(schemaVar instanceof ModalOperatorSV) {            
	    final ModalOperatorSV modalOpSV = (ModalOperatorSV)schemaVar;
	    final IteratorOfModality it = modalOpSV.getModalities().iterator();
	    assert modalOpSV instanceof ModalOperatorSV;
                out.append ( "\\modalOperator { " );
	    String sep = "";
	    while (it.hasNext()) {
		final Operator op = (Operator)it.next();
		out.append ( sep );
		out.append ( op.name() );
		sep = ", ";
	    }
	    out.append(" } " + modalOpSV.name());
	} else if(schemaVar instanceof TermSV) {
	    out.append ("\\term");
	} else if(schemaVar instanceof FormulaSV) {
	    out.append ("\\formula");
	} else if(schemaVar instanceof UpdateSV) {
	    out.append("\\update");
	} else if(schemaVar instanceof ProgramSV) {
	    out.append ("\\program");
	} else if(schemaVar instanceof VariableSV) {
	    out.append ("\\variables");
	} else if(schemaVar instanceof SkolemTermSV) {
	    out.append ("\\skolemTerm");
	} else {
	    out.append ("?");
	}                       
	writeSVModifiers(out, schemaVar);
	if(!(schemaVar instanceof FormulaSV || schemaVar instanceof UpdateSV)) {
	    out.append(" " + schemaVar.sort());
	}
	out.append(  " " + schemaVar.name() );
    }
}
