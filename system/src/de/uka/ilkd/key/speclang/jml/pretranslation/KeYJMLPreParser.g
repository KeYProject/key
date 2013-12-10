// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

parser grammar KeYJMLPreParser;

options {
    k = 1;     //do not change - interplay with lexer depends on k=1!
    tokenVocab = KeYJMLPreLexer;
}

@rulecatch { }

@header {
    package de.uka.ilkd.key.speclang.jml.pretranslation;

    import java.io.StringReader;
    import java.util.ArrayList;
    import java.util.Iterator;
    import java.util.List;

    import de.uka.ilkd.key.collection.*;
    import de.uka.ilkd.key.java.Position;
    import de.uka.ilkd.key.speclang.*;
    import de.uka.ilkd.key.speclang.translation.*;
    import de.uka.ilkd.key.ldt.HeapLDT;
    import de.uka.ilkd.key.logic.Name;
    import de.uka.ilkd.key.logic.TermBuilder;

    import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassAxiom;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLClassInv;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLDepends;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLFieldDecl;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLInitially;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLLoopSpec;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMethodDecl;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLRepresents;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSetStatement;
    import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
}

@members {
    private KeYJMLPreLexer lexer;
    private SLTranslationExceptionManager excManager;
    private ImmutableSet<PositionedString> warnings
	= DefaultImmutableSet.<PositionedString>nil();


    private KeYJMLPreParser(KeYJMLPreLexer lexer,
                            String fileName,
                            Position offsetPos) {
	this(new CommonTokenStream(lexer));
	this.lexer      = lexer;
	this.excManager = new SLTranslationExceptionManager(this,
							    fileName,
							    offsetPos);
    }


    public KeYJMLPreParser(String comment,
			   String fileName,
			   Position offsetPos) {
	this(new KeYJMLPreLexer(new ANTLRStringStream(comment)),
	     fileName,
	     offsetPos);
    }


    private PositionedString createPositionedString(String text,
						    Token t) {
	return excManager.createPositionedString(text, t);
    }


    private void raiseError(String msg) throws SLTranslationException {
        throw excManager.createException(msg);
    }


    private void raiseNotSupported(String feature)
		throws SLTranslationException {
	PositionedString warning
		= excManager.createPositionedString(feature + " not supported");
	warnings = warnings.add(warning);
    }


    public ImmutableList<TextualJMLConstruct> parseClasslevelComment()
		throws SLTranslationException {
        try {
            return classlevel_comment();
        } catch(RecognitionException e) {
	    throw excManager.convertException(e);
        }
    }


    public ImmutableList<TextualJMLConstruct> parseMethodlevelComment()
		throws SLTranslationException {
        try {
            return methodlevel_comment();
        } catch(RecognitionException e) {
	    throw excManager.convertException(e);
        }
    }


    public ImmutableSet<PositionedString> getWarnings() {
	return warnings;
    }

    private PositionedString flipHeaps(String declString, PositionedString result) {
       return flipHeaps(declString, result, false);
    }

    private PositionedString flipHeaps(String declString, PositionedString result, boolean allowPreHeaps) {
      String t = result.text;
      String p = declString+" ";

      List<Name> validHeapNames = new ArrayList<Name>();

      for(Name heapName : HeapLDT.VALID_HEAP_NAMES) {
         validHeapNames.add(heapName);
         if(allowPreHeaps) {
           validHeapNames.add(new Name(heapName.toString()+"AtPre"));
        }
      }
      for(Name heapName : validHeapNames) {
        t = t.trim();
	String l = "<"+heapName+">";
        if(t.startsWith(l)) {
           p = l + p;
           t = t.substring(l.length());
        }
        result = new PositionedString(t, result.fileName, result.pos);
      }
      result = result.prepend(p);
      return result;
    }

}



//-----------------------------------------------------------------------------
//comments
//-----------------------------------------------------------------------------

classlevel_comment
	returns [ImmutableList<TextualJMLConstruct> result
		 = ImmutableSLList.<TextualJMLConstruct>nil()]
	throws SLTranslationException
@init {
    mods = ImmutableSLList.<String>nil();
}
:
    (
        options { greedy = false; }
    	:
    	mods=modifiers
    	list=classlevel_element[mods]
    	{
	    if(list!=null) {
		result = result.append(list);
	    }
	}
    )* EOF
;


classlevel_element[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
        result=class_invariant[mods]
    |   (accessible_keyword expression) => result=depends_clause[mods]
    |   result=method_specification[mods]
    |   result=field_or_method_declaration[mods]
    |   result=represents_clause[mods]
    |   result=history_constraint[mods]
    |   result=initially_clause[mods]
    |   result=class_axiom[mods]
    |   result=monitors_for_clause[mods]
    |   result=readable_if_clause[mods]
    |   result=writable_if_clause[mods]
    |   result=datagroup_clause[mods]
    |   result=set_statement[mods]    //RecodeR workaround
    |   result=assert_statement[mods] //RecodeR workaround
    |   result=assume_statement[mods] //RecodeR workaround
    |   result=nowarn_pragma[mods]
    |   EOF
;


methodlevel_comment
	returns [ImmutableList<TextualJMLConstruct> result
		 = ImmutableSLList.<TextualJMLConstruct>nil()]
	throws SLTranslationException
@init {
    mods = ImmutableSLList.<String>nil();
}
:
    (
	mods=modifiers
	list=methodlevel_element[mods]  { result = result.append(list); }
    )* EOF
;


methodlevel_element[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
        result=field_or_method_declaration[mods]
    |   result=set_statement[mods]
    |   result=loop_specification[mods]
    |   result=assert_statement[mods]
    |   result=assume_statement[mods]
    |   result=nowarn_pragma[mods]
    |   result=block_specification[mods]
;



//-----------------------------------------------------------------------------
//modifiers
//-----------------------------------------------------------------------------

modifiers
	returns [ImmutableList<String> result = ImmutableSLList.<String>nil()]
	throws SLTranslationException
:
    (
	options { greedy = true; }
	:
	s=modifier  { result = result.append(s); }
    )*
;


modifier returns [String result = null]:
        abs=ABSTRACT            { result = abs.getText(); }
    |   fin=FINAL               { result = fin.getText(); }
    |   gho=GHOST               { result = gho.getText(); }
    |   hel=HELPER              { result = hel.getText(); }
    |   ins=INSTANCE            { result = ins.getText(); }
    |   mod=MODEL               { result = mod.getText(); }
    |   nnu=NON_NULL            { result = nnu.getText(); }
    |   nul=NULLABLE            { result = nul.getText(); }
    |   nld=NULLABLE_BY_DEFAULT { result = nld.getText(); }
    |   pri=PRIVATE             { result = pri.getText(); }
    |   pro=PROTECTED           { result = pro.getText(); }
    |   pub=PUBLIC              { result = pub.getText(); }
    |   pur=PURE                { result = pur.getText(); }
    |   stp=STRICTLY_PURE       { result = stp.getText(); }
    |   spr=SPEC_PROTECTED      { result = spr.getText(); }
    |   spu=SPEC_PUBLIC         { result = spu.getText(); }
    |   sta=STATIC              { result = sta.getText(); }
    |   tst=TWO_STATE           { result = tst.getText(); }
    |   nst=NO_STATE            { result = nst.getText(); }
    |   sjm=SPEC_JAVA_MATH      { result = sjm.getText(); }
    |   ssm=SPEC_SAVE_MATH      { result = ssm.getText(); }
    |   sbm=SPEC_BIGINT_MATH    { result = sbm.getText(); }
    |   cjm=CODE_JAVA_MATH      { result = cjm.getText(); }
    |   csm=CODE_SAVE_MATH      { result = csm.getText(); }
    |   cbm=CODE_BIGINT_MATH    { result = cbm.getText(); }
;



//-----------------------------------------------------------------------------
//class invariants and alike
//-----------------------------------------------------------------------------

class_invariant[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
@init {
    String name = null;
}
:
    invariant_keyword
//    (name=axiom_name)?
    ps=expression
    {
	TextualJMLClassInv inv = name == null ? new TextualJMLClassInv(mods, ps) : new TextualJMLClassInv(mods, ps, name);
	result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(inv);
    }
;

/** Introduce a user-given name to axiom-like declarations. */
axiom_name returns [String result = null] throws SLTranslationException
:
    AXIOM_NAME_BEGIN id=IDENT AXIOM_NAME_END
    { result = id.getText(); }
;


invariant_keyword
:
        INVARIANT
    |   INVARIANT_RED
;


class_axiom[ImmutableList<String> mods]
            returns [ImmutableList<TextualJMLConstruct> result = null]
                     throws SLTranslationException
:
    AXIOM ps=expression
    {
                         TextualJMLClassAxiom ax = new TextualJMLClassAxiom(mods, ps);
                         result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ax);
                         // axiom statements may not be prefixed with any modifiers (see Sect. 8 of the JML reference manual)
                         if (!mods.isEmpty())
                             raiseNotSupported("modifiers in axiom clause");
    }
                     ;

initially_clause[ImmutableList<String> mods]
        returns [ImmutableList<TextualJMLConstruct> result = null]
        throws SLTranslationException
:
    INITIALLY ps=expression
    {
    TextualJMLInitially ini = new TextualJMLInitially(mods, ps);
    result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ini);
    for (String s: mods) {
        if (!(s.equals("public")||s.equals("private")||s.equals("protected")))
            raiseNotSupported("modifier "+s+" in initially clause");
        }
    }
;

//-----------------------------------------------------------------------------
//method specifications
//-----------------------------------------------------------------------------

method_specification[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init {
    list = ImmutableSLList.<TextualJMLConstruct>nil();
    result = r;
}
@after { r = result; }
:
    (also_keyword)*
    result=spec_case[mods]
    (
	options { greedy = true; }
	:
	(also_keyword)+ list=spec_case[ImmutableSLList.<String>nil()]
	{
	    result = result.append(list);
	}
    )*
;


also_keyword
:
	ALSO
    |	FOR_EXAMPLE
    |   IMPLIES_THAT
;


spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
	result=lightweight_spec_case[mods]
    | 	result=heavyweight_spec_case[mods]
;



//-----------------------------------------------------------------------------
//lightweight specification cases
//-----------------------------------------------------------------------------

lightweight_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    result=generic_spec_case[mods, Behavior.NONE]
;



//-----------------------------------------------------------------------------
//heavyweight specification cases
//-----------------------------------------------------------------------------

heavyweight_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init {
    result = r;
}
@after { r = result; }
:
    (s=modifier  { mods = mods.append(s); })?
    (
	    result=behavior_spec_case[mods]
	    |   result=break_behavior_spec_case[mods]
	    |   result=continue_behavior_spec_case[mods]
	    |   result=exceptional_behavior_spec_case[mods]
	|   result=normal_behavior_spec_case[mods]
	|   result=model_behavior_spec_case[mods]
	|   result=return_behavior_spec_case[mods]
    )
;


behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    behavior_keyword
    result=generic_spec_case[mods, Behavior.BEHAVIOR]
;


behavior_keyword
:
	BEHAVIOR
    | 	BEHAVIOUR
;


normal_behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    normal_behavior_keyword
    result=generic_spec_case[mods, Behavior.NORMAL_BEHAVIOR]
;


normal_behavior_keyword
:
	NORMAL_BEHAVIOR
    | 	NORMAL_BEHAVIOUR
;

model_behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    model_behavior_keyword
    result=generic_spec_case[mods, Behavior.MODEL_BEHAVIOR]
;


model_behavior_keyword
:
      MODEL_BEHAVIOR
    | MODEL_BEHAVIOUR
;

exceptional_behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    exceptional_behavior_keyword
    result=generic_spec_case[mods, Behavior.EXCEPTIONAL_BEHAVIOR]
;


exceptional_behavior_keyword
:
	EXCEPTIONAL_BEHAVIOR
    |	EXCEPTIONAL_BEHAVIOUR
;



//-----------------------------------------------------------------------------
//generic specification cases
//-----------------------------------------------------------------------------

generic_spec_case[ImmutableList<String> mods, Behavior b]
	returns [ImmutableList<TextualJMLConstruct> r
		 = ImmutableSLList.<TextualJMLConstruct>nil()]
	throws SLTranslationException
@init {
    result = r;
}
@after { r = result; }
:
    (abbrvs=spec_var_decls)?
    (requires=spec_header
       ( options { greedy = true; }
	 : result = generic_spec_body[mods, b] )?
        {
		if (result.isEmpty()) {
		      result = result.append(new TextualJMLSpecCase(mods, b));
	        }

	        for(Iterator<TextualJMLConstruct> it = result.iterator();
                    it.hasNext(); ) {
                        TextualJMLSpecCase sc = (TextualJMLSpecCase) it.next();
                        sc.addRequires(requires);
			if (abbrvs!=null) {
				for (PositionedString[] pz: abbrvs) {
					sc.addAbbreviation(pz);
			    }
			}
	        }
        }
    | result = generic_spec_body[mods, b]
    )
;


spec_var_decls
	returns [ ImmutableList<PositionedString[\]> result = ImmutableSLList.<PositionedString[\]>nil() ]
throws SLTranslationException
:
    (
            pz=old_clause
            { result = result.append(pz); }
            |
	    FORALL ps=expression
    {
	raiseNotSupported("specification variables");
    }
    )+
;


spec_header
	returns [ImmutableList<PositionedString> result
		 = ImmutableSLList.<PositionedString>nil()]
	throws SLTranslationException
:
    (
	options { greedy = true; }
	:
	ps=requires_clause  { result = result.append(ps); }
    )+
;


requires_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    requires_keyword result=expression { result = flipHeaps("requires", result); }
;


requires_keyword
:
    REQUIRES |
    REQUIRES_RED
;


generic_spec_body[ImmutableList<String> mods, Behavior b]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init {
    TextualJMLSpecCase sc;
    result = r;
}
@after { r = result; }
:
    result=simple_spec_body[mods, b]
    |
    (
        NEST_START
	result=generic_spec_case_seq[mods, b]
	NEST_END
    )
;


generic_spec_case_seq[ImmutableList<String> mods, Behavior b]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init {
    result = r;
}
@after { r = result; }
:
    result=generic_spec_case[mods, b]
    (
        (also_keyword)+
        list=generic_spec_case[mods, b]
        {
            result = result.append(list);
        }
    )*
;


simple_spec_body[ImmutableList<String> mods, Behavior b]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
@init {
    TextualJMLSpecCase sc = new TextualJMLSpecCase(mods, b);
    result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(sc);
}
:
    (
	options { greedy = true; }
	:
	simple_spec_body_clause[sc, b]
    )+
;


simple_spec_body_clause[TextualJMLSpecCase sc, Behavior b]
	throws SLTranslationException
@init {
    PositionedString[] pss;
}
:
    (
	    ps=assignable_clause     { sc.addAssignable(ps); }
	|   ps=accessible_clause     { sc.addAccessible(ps); }
	|   ps=ensures_clause        { sc.addEnsures(ps); }
	|   ps=signals_clause        { sc.addSignals(ps); }
	|   ps=signals_only_clause   { sc.addSignalsOnly(ps); }
	|   ps=diverges_clause       { sc.addDiverges(ps); }
	|   ps=measured_by_clause    { sc.addMeasuredBy(ps); }
	|   ps=name_clause           { sc.addName(ps); }
	|   captures_clause
	|   when_clause
	|   working_space_clause
	|   duration_clause
	|   ps=breaks_clause         { sc.addBreaks(ps); }
	|   ps=continues_clause      { sc.addContinues(ps); }
	|   ps=returns_clause        { sc.addReturns(ps); }
    )
    {
	if(b == Behavior.EXCEPTIONAL_BEHAVIOR
	   && !sc.getEnsures().isEmpty()) {
	    raiseError("ensures not allowed in exceptional behavior.");
	} else if(b == Behavior.NORMAL_BEHAVIOR
	          && !sc.getSignals().isEmpty()) {
	    raiseError("signals not allowed in normal behavior.");
	} else if(b == Behavior.NORMAL_BEHAVIOR
	          && !sc.getSignalsOnly().isEmpty()) {
	        raiseError("signals_only not allowed in normal behavior.");
	} else if(b == Behavior.NORMAL_BEHAVIOR
	          && !sc.getBreaks().isEmpty()) {
		raiseError("breaks not allowed in normal behavior.");
	} else if(b == Behavior.NORMAL_BEHAVIOR
	          && !sc.getContinues().isEmpty()) {
		raiseError("continues not allowed in normal behavior.");
	} else if(b == Behavior.NORMAL_BEHAVIOR
	          && !sc.getReturns().isEmpty()) {
		raiseError("returns not allowed in normal behavior.");
	}
    }
;



//-----------------------------------------------------------------------------
//simple specification body clauses
//-----------------------------------------------------------------------------

assignable_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    assignable_keyword result=expression { result = flipHeaps("assignable", result); }
;


assignable_keyword
:
	ASSIGNABLE
    |   ASSIGNABLE_RED
    |   MODIFIABLE
    |   MODIFIABLE_RED
    |   MODIFIES
    |   MODIFIES_RED
;


accessible_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    accessible_keyword result=expression { result = flipHeaps("accessible", result, true); }
;


accessible_keyword
:
        ACCESSIBLE
    |   ACCESSIBLE_REDUNDANTLY
;


measured_by_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    measured_by_keyword result=expression { result = result.prepend("decreases "); }
;


measured_by_keyword
:
        MEASURED_BY
    |   MEASURED_BY_REDUNDANTLY
;


ensures_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    ensures_keyword result=expression { result = flipHeaps("ensures", result); }
;


ensures_keyword
:
	ENSURES
    |   ENSURES_RED
;


signals_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    signals_keyword result=expression { result = result.prepend("signals "); }
;


signals_keyword
:
	SIGNALS
    |   SIGNALS_RED
    |   EXSURES
    |   EXSURES_RED
;


signals_only_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    signals_only_keyword result=expression { result = result.prepend("signals_only "); }
;


signals_only_keyword
:
	SIGNALS_ONLY
    |   SIGNALS_ONLY_RED
;


diverges_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    diverges_keyword result=expression
;


diverges_keyword
:
	DIVERGES
    |   DIVERGES_RED
;


captures_clause throws SLTranslationException
:
    captures_keyword ps=expression
    {
	raiseNotSupported("captures clauses");
    }
;


captures_keyword
:
	CAPTURES
    |   CAPTURES_RED
;


name_clause
	returns [PositionedString result = null]
	throws SLTranslationException
:
    spec=SPEC_NAME name=STRING_LITERAL SEMICOLON
    {
	result=createPositionedString(name.getText(), spec);
    }
;


when_clause throws SLTranslationException
:
    when_keyword ps=expression
    {
	raiseNotSupported("when clauses");
    }
;


when_keyword
:
	WHEN
    |   WHEN_RED
;


working_space_clause throws SLTranslationException
:
    working_space_keyword ps=expression
    {
	raiseNotSupported("working_space clauses");
    }
;


working_space_keyword
:
	WORKING_SPACE
    |   WORKING_SPACE_RED
;


duration_clause throws SLTranslationException
:
    duration_keyword ps=expression
    {
	raiseNotSupported("duration clauses");
    }
;


duration_keyword
:
	DURATION
    |   DURATION_RED
;

old_clause
	returns [ PositionedString[\] result = new PositionedString[3\] ]
	throws SLTranslationException
:
	OLD mods=modifiers
	type=IDENT
	name=IDENT
	init=INITIALISER
	{ // modifiers are ignored, don't make any sense here
	  result[0] = new PositionedString(type.getText(),type);
	  result[1] = new PositionedString(name.getText(),name);
	  result[2] = new PositionedString(init.getText().substring(2),init);
    }
;


field_or_method_declaration[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
:
    type=IDENT 	name=IDENT 
    ( (LPAREN) => methodDecl = method_declaration[mods, type, name] {result = methodDecl;}
      |
      fieldDecl = field_declaration[mods, type, name] {result = fieldDecl;}
    ) 
;


//-----------------------------------------------------------------------------
//field declarations
//-----------------------------------------------------------------------------

field_declaration[ImmutableList<String> mods, Token type, Token name]
	returns [ImmutableList<TextualJMLConstruct> result = null]
@init {
    StringBuffer sb = new StringBuffer(type.getText() + " " + name.getText());
    String s;
}
:
    (t=EMPTYBRACKETS { sb.append(t.getText()); })*
    (
	    init=initialiser  { sb.append(init); }
	|   semi=SEMICOLON    { sb.append(semi.getText()); }
    )
    {
        PositionedString ps = createPositionedString(sb.toString(), type);
	TextualJMLFieldDecl fd = new TextualJMLFieldDecl(mods, ps);
	result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(fd);
    }
;



//-----------------------------------------------------------------------------
//method declarations
//-----------------------------------------------------------------------------

method_declaration[ImmutableList<String> mods, Token type, Token name]
	returns [ImmutableList<TextualJMLConstruct> result = null]
@init {
    StringBuffer sb = new StringBuffer(type.getText() + " " + name.getText());
    StringBuffer sbDefinition = new StringBuffer();
    String s;
}
:
    params=param_list   { sb.append(params); }
    (
	    body=BODY  	    { sbDefinition.append(body.getText()); }
	|   semi=SEMICOLON
    )
    {
	sb.append(";");
        PositionedString ps = createPositionedString(sb.toString(), type);
        PositionedString psDefinition = null;
        if(sbDefinition.length() > 0) {
          String paramsString = params.trim();
          String bodyString = new String(sbDefinition).trim();
          assert paramsString.charAt(0) == '(' && paramsString.charAt(paramsString.length()-1) == ')';
          paramsString = paramsString.substring(1, paramsString.length()-1).trim();
          if(!paramsString.equals("")) {
            StringBuffer stmp = new StringBuffer();
            for(String t : paramsString.split(",")) {
              t = t.trim();
              t = t.substring(t.indexOf(" ")+1);
              if(stmp.length() > 0) stmp.append(", ");
              stmp.append(t);
            }
            paramsString = "("+new String(stmp) +")";
          }else{
            paramsString = "()";
          }
          assert bodyString.charAt(0) == '{' && bodyString.charAt(bodyString.length()-1) == '}';
          bodyString = bodyString.substring(1, bodyString.length()-1).trim();
          assert bodyString.startsWith("return ");
          bodyString = bodyString.substring(bodyString.indexOf(" ") + 1);
          // TODO Other heaps? There is only one return statement.....
          psDefinition = createPositionedString("<heap> "+name.getText() +
               paramsString + " == "+bodyString, type);
               
        }

	TextualJMLMethodDecl md
		= new TextualJMLMethodDecl(mods, ps, name.getText(), psDefinition);
	result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(md);
    }
;

param_list returns [String s = null]
@init {
    final StringBuilder text = new StringBuilder();
}
@after {
    s = text.toString();
}
    :
        t=LPAREN { text.append(t.getText()); }
        (
            param=param_decl { text.append(param); }
            (
                t=COMMA
                param=param_decl
                { text.append(t.getText() + param); }
            )*
        )?
        t=RPAREN { text.append(t.getText()); }
    ;

param_decl returns [String s = null]
@init {
    final StringBuilder text = new StringBuilder();
}
@after {
    s = text.toString();
}
    :
        (
             t=(NON_NULL | NULLABLE)
             {
                text.append("/*@" + t.getText() + "@*/");
             }
        )?
        t=IDENT
        {
            text.append(t.getText() + " ");
        }
        t=IDENT
        {
            text.append(t.getText());
        }
    ;


//-----------------------------------------------------------------------------
//represents clauses
//-----------------------------------------------------------------------------


represents_clause[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    represents_keyword ps=expression
    {
	TextualJMLRepresents rc
		= new TextualJMLRepresents(mods, ps.prepend("represents "));
	result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(rc);
    }
;


represents_keyword
:
        REPRESENTS
    |   REPRESENTS_RED
;



//-----------------------------------------------------------------------------
//classlevel depends clauses (custom extension of JML)
//-----------------------------------------------------------------------------

depends_clause[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    accessible_keyword ps=expression
    {
	TextualJMLDepends d
		= new TextualJMLDepends(mods, flipHeaps("depends", ps, false));
	result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(d);
    }
;



//-----------------------------------------------------------------------------
//unsupported classlevel stuff
//-----------------------------------------------------------------------------

history_constraint[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    constraint_keyword ps=expression
    {
	raiseNotSupported("history constraints");
	result = ImmutableSLList.<TextualJMLConstruct>nil();
    }
;


constraint_keyword
:
        CONSTRAINT
    |   CONSTRAINT_RED
;



monitors_for_clause[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    MONITORS_FOR ps=expression
    {
	raiseNotSupported("monitors_for clauses");
	result = ImmutableSLList.<TextualJMLConstruct>nil();
    }
;


readable_if_clause[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    READABLE ps=expression
    {
	raiseNotSupported("readable-if clauses");
	result = ImmutableSLList.<TextualJMLConstruct>nil();
    }
;


writable_if_clause[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    WRITABLE ps=expression
    {
	raiseNotSupported("writable-if clauses");
	result = ImmutableSLList.<TextualJMLConstruct>nil();
    }
;


datagroup_clause[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    in_group_clause | maps_into_clause
;


in_group_clause  throws SLTranslationException
:
    in_keyword ps=expression
    {
	raiseNotSupported("in-group clauses");
    }
;


in_keyword
:
	IN
    | 	IN_RED
;


maps_into_clause throws SLTranslationException
:
    maps_keyword ps=expression
    {
	raiseNotSupported("maps-into clauses");
    }
;


maps_keyword
:
	MAPS
    | 	MAPS_RED
;


nowarn_pragma[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    NOWARN ps=expression
    {
	raiseNotSupported("nowarn pragmas");
	result = ImmutableSLList.<TextualJMLConstruct>nil();
    }
;



//-----------------------------------------------------------------------------
//set statements
//-----------------------------------------------------------------------------

set_statement[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
:
    SET ps=expression
    {
	TextualJMLSetStatement ss = new TextualJMLSetStatement(mods, ps);
	result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ss);
    }
;



//-----------------------------------------------------------------------------
//loop specifications
//-----------------------------------------------------------------------------

loop_specification[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
@init {
   TextualJMLLoopSpec ls = new TextualJMLLoopSpec(mods);
   result = ImmutableSLList.<TextualJMLConstruct>nil().prepend(ls);
}
:
    ps=loop_invariant       { ls.addInvariant(ps); }
    (
	options { greedy = true; }
	:
            ps=loop_invariant       { ls.addInvariant(ps); }
        |   ps=assignable_clause    { ls.addAssignable(ps); }
        |   ps=variant_function     { ls.setVariant(ps); }
    )*
;


loop_invariant returns [PositionedString r = null]
@init { result = r; }
@after { r = result; }
:
    maintaining_keyword result=expression { result = flipHeaps("", result); }
;

maintaining_keyword
:
        MAINTAINING
    |   MAINTAINING_REDUNDANTLY
    |   LOOP_INVARIANT
    |   LOOP_INVARIANT_REDUNDANTLY
;


variant_function returns [PositionedString r = null]
@init { result = r; }
@after { r = result; }
:
    decreasing_keyword result=expression { result = result.prepend("decreases "); }
;


decreasing_keyword
:
        DECREASING
    |   DECREASING_REDUNDANTLY
    |   DECREASES
    |   DECREASES_REDUNDANTLY
;



//-----------------------------------------------------------------------------
//unsupported methodlevel stuff
//-----------------------------------------------------------------------------


assume_statement[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    assume_keyword ps=expression
    {
        raiseNotSupported("assume statements");
	result = ImmutableSLList.<TextualJMLConstruct>nil();
    }
;


assume_keyword
:
	ASSUME
    |	ASSUME_REDUNDANTLY
;



//-----------------------------------------------------------------------------
//expressions
//-----------------------------------------------------------------------------


expression returns [PositionedString result = null]
@init {
    int parenthesesCounter = 0;
    final StringBuilder text = new StringBuilder();
    Token begin = null;
}
:
    (
        (
            t=LPAREN { parenthesesCounter++; }
        |   t=RPAREN { parenthesesCounter--; }
        |   { parenthesesCounter > 0 }? t=SEMICOLON
        |   t=~(LPAREN | RPAREN | SEMICOLON)
        )
        { if (begin == null) { begin = t; } text.append(" " + t.getText()); }
    )*
    { parenthesesCounter == 0 }? t=SEMICOLON { if (begin == null) { begin = t; } text.append(t.getText()); }
    {
	result = createPositionedString(text.toString(), begin);
    }
;

initialiser returns [String s = null]
    :
        EQUALITY ps=expression { s = "=" + ps.text; }
    ;


//-----------------------------------------------------------------------------
//block specifications
//-----------------------------------------------------------------------------

block_specification[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:

    result=method_specification[mods]
;


assert_statement[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> result = null]
	throws SLTranslationException
:
    assert_keyword ps=expression
    {
	result = ImmutableSLList.<TextualJMLConstruct>nil().append(TextualJMLSpecCase.assert2blockContract(mods,ps));
    }
;


assert_keyword
:
	ASSERT
    |	ASSERT_REDUNDANTLY
;

breaks_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
	breaks_keyword result=expression { result = result.prepend("breaks "); }
;


breaks_keyword
:
	BREAKS
;


continues_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
	continues_keyword result=expression { result = result.prepend("continues "); }
;


continues_keyword
:
	CONTINUES
;


returns_clause
	returns [PositionedString r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
	returns_keyword result=expression { result = result.prepend("returns "); }
;


returns_keyword
:
	RETURNS
;


break_behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    break_behavior_keyword
    result=generic_spec_case[mods, Behavior.BREAK_BEHAVIOR]
;


break_behavior_keyword
:
	BREAK_BEHAVIOR
    |	BREAK_BEHAVIOUR
;


continue_behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    continue_behavior_keyword
    result=generic_spec_case[mods, Behavior.CONTINUE_BEHAVIOR]
;


continue_behavior_keyword
:
	CONTINUE_BEHAVIOR
    |	CONTINUE_BEHAVIOUR
;


return_behavior_spec_case[ImmutableList<String> mods]
	returns [ImmutableList<TextualJMLConstruct> r = null]
	throws SLTranslationException
@init { result = r; }
@after { r = result; }
:
    return_behavior_keyword
    result=generic_spec_case[mods, Behavior.RETURN_BEHAVIOR]
;


return_behavior_keyword
:
	RETURN_BEHAVIOR
    |	RETURN_BEHAVIOUR
;