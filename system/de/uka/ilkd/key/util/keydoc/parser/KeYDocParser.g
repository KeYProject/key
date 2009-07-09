// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
header { package de.uka.ilkd.key.util.keydoc.parser; import java.util.LinkedList; }

class KeYDocParser extends Parser;

options { k=1; buildAST=true; importVocab= KeYDocLexer; exportVocab= KeYDocParser;}
{
    boolean nl= true;  // Do we have a newline situation?
    // important due to several reasons:
    // - tags are only allowered in newline situations
    // - STAR and WS should be ignored in newline situations
    
    boolean first= true; // true if this is the first line of text
    public int firstLength=0; // How long is the first line of Text?
    public StringBuffer htmlText= new StringBuffer();

    public StringBuffer keyText= new StringBuffer();
    
    public LinkedList links= new LinkedList();
}


/* ***************** ROOT RULES **********************/

startRule:
        (options {greedy=true;}: WS! | NEWLINE!)* 
        (options {greedy=true;}: OPENDOC^
        doc
        CLOSEDOC!)? {nl=false;} (keytext!)*;

// Without recursive definition of doc, tag could never end with CLOSEDOC
doc:    {(nl==true)}? tag (NEWLINE! {nl=true;} doc)? |
        text (doc)?
        ;


/* ***************** END ROOT RULES ******************/



/* ***************** TEXT RULES **********************/

text: (LEFTBRACKET AT) => linktag {nl=false; links.add(new Integer(htmlText.length()));} | normaltext!;  


normaltext {String temp=null;}: 
            (temp=commontext {htmlText.append(temp); if (first){  if(temp.equals(".") || temp.equals("!") || temp.equals("?")) {firstLength= htmlText.length(); first=false;}} if (!temp.equals("")) nl=false; } |
            (   QUOTE {htmlText.append("\""); } |
                MT {htmlText.append(">"); } |
                RIGHTBRACKET {htmlText.append("}"); } |
                LEFTBRACKET {htmlText.append("{"); } ) {nl=false;}
            )  |
            
            NEWLINE! {nl= true;  htmlText.append("<br>"); } 
            ;

/* ***************** END TEXT RULES *****************/



/* ***************** TAG RULES ***********************/

tag:    AT!
        (
            PROVABLE^ WS! IDENT (WS!)* |
            
            SEE^ separator (keydoclink (WS! descriptionr)? | http (descriptionr)? | descriptionq (WS!)*)  |
            
            VERSION^  WS! dotint (WS!)* |
            
            SINCE^ WS! dotint (WS!)* |

            AUTHOR^ WS! descriptionr  |
            
            DEPRECATED^ (WS!)* |
            
            STATISTIC^ WS! IDENT WS! (IDENT | INT) (WS!)* |
            
        )
        ;




linktag: LEFTBRACKET! AT! LINK^ separator (keydoclink (separator descriptionr)?  | http (descriptionr)?)  RIGHTBRACKET!;

separator: (WS | NEWLINE)!;

/* ***************** END TAG RULES *******************/



/* ***************** TEXT STUFF **********************/


keydoclink:
        (SLASH)? IDENT (SLASH IDENT)* DOT IDENT
        ;


descriptionq {String dummy;}: QUOTE (dummy= commontext | MT | RIGHTBRACKET | LEFTBRACKET )+ QUOTE ; // dummy to shut up warnings about return values.

descriptionr {String dummy;}:
    (dummy=commontext | QUOTE | MT | LEFTBRACKET)+;

http {String dummy;}: HTTPSTART ( dummy=commontext | QUOTE | RIGHTBRACKET | LEFTBRACKET  )+  MT;

commontext returns[String ct]{ct=null;}:
        ot: OTHERTEXT { ct=ot.getText();} |
        id: IDENT  {ct=id.getText();} |
        in: INT  {ct=in.getText();} |
        dt: DOT  {ct=dt.getText();} |
        ws: WS  {if (!nl) ct=ws.getText(); else ct="";} |
        ha: HASH  {ct=ha.getText();} |
        sl: SLASH  {ct=sl.getText();} |
        ta: TAB {if (!nl) ct=ta.getText(); else ct="";} |
        st: STAR  {if (!nl) ct=st.getText(); else ct="";} |
        at: AT {ct=at.getText();} |
        op: OPENDOC {ct=op.getText();} |
        pr: PROVABLE {ct=pr.getText();} |
        se: SEE {ct=se.getText();} |
        ve: VERSION {ct=ve.getText();} |
        si: SINCE {ct=si.getText();} |
        au: AUTHOR {ct=au.getText();} |
        de: DEPRECATED {ct=de.getText();} |
        sa: STATISTIC {ct=sa.getText();} |
        ht: HTTPSTART {ct=ht.getText();} |  
        li: LINK {ct=li.getText();};


dotint: 
        INT (DOT INT)*;

/* ***************** END TEXT STUFF ******************/


keytext {String temp=null;}: 
            temp=commontext {if (temp.equals("<")) keyText.append("&lt;"); else keyText.append(temp);} |
            QUOTE {keyText.append("\"");} |
            MT {keyText.append(">");} |
            RIGHTBRACKET {keyText.append("}"); } |
            LEFTBRACKET {keyText.append("{"); } |
            CLOSEDOC {keyText.append("*/"); } |
            NEWLINE {keyText.append("\n");}            
            ;
