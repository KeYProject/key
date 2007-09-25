/*%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

        Copyright (c) Non, Inc. 1997 -- All Rights Reserved

PROJECT:        C Compiler
MODULE:         Parser
FILE:           stdc.g

AUTHOR:         John D. Mitchell (john@non.net), Jul 12, 1997

REVISION HISTORY:

        Name    Date            Description
        ----    ----            -----------
        JDM     97.07.12        Initial version.
        JTC     97.11.18        Declaration vs declarator & misc. hacking.
        JDM     97.11.20        Fixed:  declaration vs funcDef,
                                        parenthesized expressions,
                                        declarator iteration,
                                        varargs recognition,
                                        empty source file recognition,
                                        and some typos.


DESCRIPTION:

        This grammar supports the Standard C language.

        Note clearly that this grammar does *NOT* deal with
        preprocessor functionality (including things like trigraphs)
        Nor does this grammar deal with multi-byte characters nor strings
        containing multi-byte characters [these constructs are "exercises
        for the reader" as it were :-)].

        Please refer to the ISO/ANSI C Language Standard if you believe
        this grammar to be in error.  Please cite chapter and verse in any
        correspondence to the author to back up your claim.

TODO:

        - typedefName is commented out, needs a symbol table to resolve
        ambiguity.

        - trees

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%*/
header {
package de.uka.ilkd.key.lang.clang.common.loader.parser;
}

{
import java.io.*;

import antlr.CommonAST;
import antlr.DumpASTVisitor;
import java.util.Vector;
import java.util.List;
import java.util.ArrayList;
import java.util.Map;
import java.util.HashMap;
import java.util.Iterator;
import java.util.ListIterator;
import java.util.LinkedList;
import cetus.hir.*;
import de.uka.ilkd.key.lang.clang.common.loader.util.*;
}
 

class SchemaCParser extends Parser;

options
        {
        k = 2;
        exportVocab = SCHEMAC;
        buildAST = true;
        //ASTLabelType = "TNode";

        // Copied following options from java grammar.
        codeGenMakeSwitchThreshold = 2;
        codeGenBitsetTestThreshold = 3;
        }


{
	
		
		Expression baseEnum = null,curEnum = null; 
		SchemaCLexer curLexer=null;
		boolean isFuncDef = false;
		boolean isExtern = false;	
	   	PreprocessorInfoChannel preprocessorInfoChannel = null;
        SymbolTable symtab = null;
        boolean hastypedef = false;
        Hashtable typetable = null;
        ArrayList currproc = new ArrayList();
        Declaration prev_decl = null;
        boolean old_style_func = false;
        Hashtable func_decl_list = new Hashtable();

        ParserStrategy strategy = ParserStrategy.getInstance();

        public void getPreprocessorInfoChannel(PreprocessorInfoChannel preprocChannel )
		{
        	preprocessorInfoChannel = preprocChannel;

		}
		public void setLexer(SchemaCLexer lexer){
			curLexer=lexer;
			curLexer.setParser(this);
		}
		public SchemaCLexer getLexer(){
			return curLexer;
		}
		public Vector getPragma(int a){
		 	return preprocessorInfoChannel.extractLinesPrecedingTokenNumber
								(new Integer(a));	
		}
        public void putPragma(Token sline,SymbolTable sym){
                	Vector v  = null;
                	v = getPragma(((CToken)sline).getTokenNumber());
        			Iterator iter = v.iterator();
        			Pragma p = null;
        				Annotation anote = null;
        			while(iter.hasNext()){
        				p = (Pragma)iter.next(); 
        			 	anote = new Annotation(p.str);
        				if(p.type ==Pragma.pragma)
        					anote.setPrintMethod(Annotation.print_raw_method);
        				else if(p.type ==Pragma.comment)
        					anote.setPrintMethod(Annotation.print_raw_method);
        				//sym.addStatement(new DeclarationStatement(anote));
        				if(sym instanceof CompoundStatement)
        					((CompoundStatement)sym).addStatement(new DeclarationStatement(anote));
        				else
        					sym.addDeclaration(anote);
        			}
        }
        
    // Suppport C++-style single-line comments?
    public static boolean CPPComments = true;

    public boolean isTypedefName(String name) {
        //Added by Daniel
        if (typetable == null) {return false;}
        //
		boolean returnValue = false;
		Object o = typetable.get(name);
		if(o == null){
			returnValue = false;
		}
		else{
			returnValue = true;
		}
     
      if(name.equals("__builtin_va_list"))
      	returnValue = true;
     
      
      return returnValue;     
      
    }

	
	
	
	
        int traceDepth = 0;
        public void reportError(RecognitionException ex){
          try {
            //System.err.println("ANTLR Parsing Error: "+ex + " token name:" + tokenNames[LA(1)]);
            //System.err.println("Before: ");
	    //((Printable)symtab).print(System.err);
	    //System.err.println();
	    System.err.println("ANTLR Parsing Error: "+"Exception Type: "+ex.getClass().getName());
            System.err.println("Source: "+getLexer().lineObject.getSource()+" Line:"+ex.getLine()+" Column: "+ex.getColumn() +" token name:" + tokenNames[LA(1)]);
            ex.printStackTrace(System.err);
            // OM:             
            //System.exit(1);
            throw new RuntimeException(ex);
          }
	  catch (TokenStreamException e) {
            System.err.println("ANTLR Parsing Error: "+ex);
            ex.printStackTrace(System.err);
            // OM:             
            //System.exit(1);
            throw new RuntimeException(ex);
          }
        }
        public void reportError(String s) {
            System.err.println("ANTLR Parsing Error from String: " + s);
        }
        public void reportWarning(String s) {
            System.err.println("ANTLR Parsing Warning from String: " + s);
        }
        public void match(int t) throws MismatchedTokenException {
          boolean debugging = false;

          if ( debugging ) {
           for (int x=0; x<traceDepth; x++) System.out.print(" ");
           try {
            System.out.println("Match("+tokenNames[t]+") with LA(1)="+
                tokenNames[LA(1)] + ((inputState.guessing>0)?" [inputState.guessing "+ inputState.guessing + "]":""));
           }
           catch (TokenStreamException e) {
            System.out.println("Match("+tokenNames[t]+") " + ((inputState.guessing>0)?" [inputState.guessing "+ inputState.guessing + "]":""));

           }

          }
          try {
            if ( LA(1)!=t ) {
                if ( debugging ){
                    for (int x=0; x<traceDepth; x++) System.out.print(" ");
                    System.out.println("token mismatch: "+tokenNames[LA(1)]
                                + "!="+tokenNames[t]);
                }
	        throw new MismatchedTokenException(tokenNames, LT(1), t, false, getFilename());

            } else {
                // mark token as consumed -- fetch next token deferred until LA/LT
                consume();
            }
          }
          catch (TokenStreamException e) {
          }

        }
        public void traceIn(String rname) {
          traceDepth += 1;
          for (int x=0; x<traceDepth; x++) System.out.print(" ");
          try {
            System.out.println("> "+rname+"; LA(1)==("+ tokenNames[LT(1).getType()]
                + ") " + LT(1).getText() + " [inputState.guessing "+ inputState.guessing + "]");
          }
          catch (TokenStreamException e) {
          }
        }
        public void traceOut(String rname) {
          for (int x=0; x<traceDepth; x++) System.out.print(" ");
          try {
            System.out.println("< "+rname+"; LA(1)==("+ tokenNames[LT(1).getType()]
                + ") "+LT(1).getText() + " [inputState.guessing "+ inputState.guessing + "]");
          }
          catch (TokenStreamException e) {
          }
          traceDepth -= 1;
        }

}

/*
 *	TranslationUnit
 */

translationUnit [TranslationUnit init_tunit] returns [TranslationUnit tunit]
		{ 
			/* build a new Translation Unit */
			if(init_tunit == null)
				tunit = new TranslationUnit(getLexer().originalSource);
			else
				tunit = init_tunit;
			symtab = tunit;
			typetable = new Hashtable();
			
		}
        :       ( externalList[tunit] 
        			
        		)?       /* Empty source files are allowed.  */
        		
			{//System.err.println(typetable);
			}
        ;

externalList [TranslationUnit tunit]
			{ boolean flag = true;	}
        :       ( 
        			pre_dir:PREPROC_DIRECTIVE  
					{
						String value = (pre_dir.getText()).substring(7).trim();
						putPragma(pre_dir,symtab);
						/*
						if(value.startsWith("endinclude")){
						
								flag = true;
						}
						else if(value.startsWith("startinclude")){
								
								flag = false;
						}
						*/
						Annotation anote = new Annotation(pre_dir.getText());
						tunit.addDeclaration(anote);
						anote.setPrintMethod(Annotation.print_raw_method);
						
						
						
						//elist.add(pre_dir.getText());
					}
					|
        			externalDef[tunit] 
					/*
					{
						if(flag){
							//elist.add(edef);
						}
					}
					*/
        		)+
        ;
/*
 *	Declaration
 */

externalDef [TranslationUnit tunit]
        {
			Declaration decl = null;
		}
        :
               ( "typedef" | declaration )=> 
        		decl=declaration 
        		{
        			if(decl != null){
        				/*System.err.println("Adding Declaration");
        				decl.print(System.err);
        				System.err.println("");*/
        				tunit.addDeclaration(decl);
        			}
        				
        		}
        |   ( functionPrefix )=> 
        		decl=functionDef
        		{
        			/*System.err.println("Adding Declaration");
        				decl.print(System.err);
        				System.err.println("");*/
        			tunit.addDeclaration(decl);}
        |   decl=typelessDeclaration
        		{/*System.err.println("Adding Declaration");
        				decl.print(System.err);
        				System.err.println("");*/
        			tunit.addDeclaration(decl);}
// OM:        			
//        |   asm_expr // not going to handle this now
        |   SEMI	// empty declaration - ignore it
        ;

/* these two are here because GCC allows "cat = 13;" as a valid program! */
//Need to check side effect 
functionPrefix 
                {Declarator decl = null;}
        :       ( (functionDeclSpecifiers)=> 
        					functionDeclSpecifiers
                |  //epsilon
                )
                // Passing "null" could cause a problem
                decl = declarator
                ( declaration )* (VARARGS)? ( SEMI )*
                LCURLY
        ;

/*
 *	Declaration
 */

// Type Declaration
typelessDeclaration returns [Declaration decl]
                {decl=null;
				List idlist=null;}
        :                	
        		idlist=initDeclList SEMI
        		/*
        		 * Proper constructor missing
        		 */
        		{decl = new VariableDeclaration(new ArrayList(),idlist); }
        ;

// going to ignore this
asm_expr { Expression expr1 = null;}
        :       "asm"^ 
// OM: ( SEMI )+        
                ("volatile")? LCURLY expr1=expr RCURLY ( SEMI )
        ;

/*
 *	Declaration
 */
declaration returns [Declaration bdecl]
				{bdecl=null;
				List dspec=null;
				List idlist=null;
                //System.out.println("SchemaCParser::declaration ==> ");
				}
        :       dspec=declSpecifiers
                (   
					// Pass specifier to add to Symtab
                    idlist=initDeclList
                )?
                {	if(idlist != null){
                
                		 
                		if(old_style_func){
                 			
                			Iterator iter = idlist.iterator();
                			Declarator d  = null;
                			Declaration newdecl = null;
                			while(iter.hasNext()){
                				d = (Declarator)(iter.next());
                				newdecl = new VariableDeclaration(dspec,d);
                				func_decl_list.put(d.getSymbol().toString(),newdecl);
             				
                			}
                			bdecl = null;
						/*	
							Iterator iter = idlist.iterator();
                			Declarator d  = null;
                			Declaration newdecl = null;
                			while(iter.hasNext()){
                				d = (Declarator)(iter.next());
                				newdecl = new VariableDeclaration(dspec,d);
                				symtab.addDeclaration(newdecl);
             				
                			}
                			bdecl = null;
                		*/
						}
                		else
                			bdecl = new VariableDeclaration(dspec,idlist);
                		prev_decl = null;
                	}
                	else{
                		/*
                		 * Looks like a forward declaration
                		 */
                		 
                		if(prev_decl != null){
                		
                			bdecl = prev_decl;
                			prev_decl = null;
                		}
                	}
                		 
                	hastypedef = false;
                }
// OM: (dsemi:SEMI)+                
                ( dsemi:SEMI ) {
                	
                	int sline = 0;
                	sline = dsemi.getLine();
        			
        			putPragma(dsemi,symtab);
        			
        			
                }
        ;

/*
 *	Specifier List
 */
// The main type information
declSpecifiers returns [List decls]
                { decls = new ArrayList();
                	Specifier spec = null; 
                	Specifier temp=null;}
        :       (               options { // this loop properly aborts when
                                          //  it finds a non-typedefName ID MBZ
                                          warnWhenFollowAmbig = false;
                                        } :
                  /* Modifier */
                  spec = storageClassSpecifier {decls.add(spec);}
                | /* Modifier */
                  spec = typeQualifier {decls.add(spec);}
                
                | /* SubType */
                  ( "struct" | "union" | "enum" | typeSpecifier )=>
                        temp = typeSpecifier 
                        { 
                        	decls.add(temp) ;                    		
                        }
                 // MinGW specific
                 | attributeDecl
                )+
                
        ;
/*********************************
 * Specifier                      *
 **********************************/
 

storageClassSpecifier returns [Specifier cspec]
				{cspec= null;}
        :       "auto" 
        		{cspec = Specifier.AUTO;}
        |       "register" 
        		{cspec = Specifier.REGISTER;}
        |       "typedef" 
        		{
        			cspec = Specifier.TYPEDEF;
        			hastypedef = true;
        		}
        |       cspec = functionStorageClassSpecifier
        		
        ;

functionStorageClassSpecifier  returns [Specifier type] {type= null;}
        :       "extern" {type= Specifier.EXTERN; }
        |       "static" {type= Specifier.STATIC;}
        |       "inline"  {type= Specifier.INLINE;}
        ;

typeQualifier returns [Specifier tqual] {tqual=null;}
        :       "const" 
        		{tqual = Specifier.CONST;}
        |       "volatile" 
        		{tqual = Specifier.VOLATILE;}
        ;
         

// A Type Specifier (basic type and user type)
/***************************************************
 * Should a basic type be an int value or a class ? *
 ****************************************************/
typeSpecifier returns [Specifier types]
        { types = null; 
				String tname = null;
				Expression expr1 = null;
				List tyname = null;
				boolean typedefold = false;
		}
        :       {typedefold = hastypedef;
        		hastypedef = false;
        }
        ( 		"void" {types = Specifier.VOID;}
        |       "char" {types = Specifier.CHAR;}
        |       "short" {types = Specifier.SHORT;}
        |       "int" {types = Specifier.INT;}
        |       "long" {types = Specifier.LONG;}
        |       "float" {types = Specifier.FLOAT;}
        |       "double" {types = Specifier.DOUBLE;}
        |       "signed" {types = Specifier.SIGNED;}
        |       "unsigned" {types = Specifier.UNSIGNED;}
        |       "bool" {types = Specifier.BOOL;}
        |       types = structOrUnionSpecifier
        		( options{warnWhenFollowAmbig=false;}: attributeDecl )*
        |       types = enumSpecifier
        |       types = typedefName
        |       
        		/*
        		 * Maybe unused
        		 */
        		"typeof"^ LPAREN
                ( ( typeName )=> tyname=typeName
                | expr1=expr
                )
                RPAREN
        |       "__complex" {types = Specifier.DOUBLE;}
        |
                /*
                 * SchemaVariableType
                 */
                types=typeSV //{System.out.println("SchemaCParser::typeSpecifier ==> ");}
        )
        { 
        	hastypedef = typedefold;
        }
        ;




typeSV returns [TypeSVWrapper svType]
    {
        svType = null;
    }
    :
	    { strategy.testTypeSV( LT(1).getText() )  }?
        svID:SCHEMA_ID
        {
        	try {
	            svType = strategy.getTypeSV(svID.getText());
	        }
	        catch(ParserStrategy.NotFoundException e) {
	        	throw new RuntimeException(e);
	        }
        }
        exception
          catch [SemanticException ex] {
            throw new NoViableAltException(LT(1), getFilename());
        };

typedefName returns[Specifier name] {name = null;}
        :       { isTypedefName ( LT(1).getText() ) }?
                i:ID                    
                //{ ## = #(#[NTypedefName], #i); }
                {name = new UserSpecifier(new Identifier(i.getText()));}
        ;


structOrUnion returns [int type] { type=0 ;}
        :       "struct"	{type = 1;}
        |       "union"		{type = 2;}
        ;
// A User Type
structOrUnionSpecifier returns [Specifier spec] 
				{
					ClassDeclaration decls = null;
					String name=null;
					int type=0;
					spec = null;
					int linenum = 0;
				}
        :       type=structOrUnion! 
                ( 
                	//Named stucture with body
                	( ID LCURLY )=> i:ID l:LCURLY
                		{name = i.getText();linenum = i.getLine(); putPragma(i,symtab);}
                        {
                        	String sname = null;
							if(type == 1){
									decls = new ClassDeclaration(ClassDeclaration.STRUCT,new Identifier(name));
									spec = new UserSpecifier(new Identifier("struct "+name));
							}
							else{
									decls = new ClassDeclaration(ClassDeclaration.UNION,new Identifier(name));
									spec = new UserSpecifier(new Identifier("union "+name));
							}
						
						}
                        ( structDeclarationList[decls] )?
                       {
                       		symtab.addDeclaration(decls);
                       }
                     RCURLY
                |   
                	// unnamed structure with body
                  	// This is for one time use
                	l1:LCURLY
                	{
                		name = getLexer().originalSource +"_"+ ((CToken)l1).getTokenNumber();
                		name =name.replaceAll("[.]","_");
                		name =name.replaceAll("-","_");
                		linenum = l1.getLine(); putPragma(l1,symtab);
                		if(type == 1){
							decls = new ClassDeclaration(ClassDeclaration.STRUCT,new Identifier(name));
							spec = new UserSpecifier(new Identifier("struct "+name));
						}
						else{
							decls = new ClassDeclaration(ClassDeclaration.UNION,new Identifier(name));
							spec = new UserSpecifier(new Identifier("union "+name));
						}
						
					}
                    ( structDeclarationList[decls] )?
                    {
                    	symtab.addDeclaration(decls);
                    }
                    RCURLY
                | // named structure without body
                	sou3:ID
                	{name = sou3.getText();linenum = sou3.getLine(); putPragma(sou3,symtab);}
					{	
						if(type == 1){
							spec = new UserSpecifier(new Identifier("struct "+name));
							decls = new ClassDeclaration(ClassDeclaration.STRUCT,new Identifier(name),true);
						}
						else{
							spec = new UserSpecifier(new Identifier("union "+name));
							decls = new ClassDeclaration(ClassDeclaration.UNION,new Identifier(name),true);
						}
						prev_decl = decls;
					}
					
                )
        ;

/*
 * Declarations are added to ClassDeclaration
 */ 

structDeclarationList [ClassDeclaration cdecl] {Declaration sdecl= null;SymbolTable prev_symtab = symtab;}
        :   
        	( sdecl=structDeclaration  {if(sdecl != null )cdecl.addDeclaration(sdecl);} )+
        	{
        		symtab = prev_symtab;
        	}
        ;


/*
 * A declaration
 */ 
structDeclaration returns [Declaration sdecl]
			{ 
				List bsqlist=null;
	        	List bsdlist=null;
				sdecl=null;
			}
        :      
        		bsqlist = specifierQualifierList 
        		
        		// passes specifier to put in symtab
				bsdlist = structDeclaratorList
        		 ( COMMA! )? ( SEMI! )+
        		{sdecl = new VariableDeclaration(bsqlist,bsdlist);}
        ;

/*
 * List of Specifiers
 */ 
specifierQualifierList returns [List sqlist]
               //{ int specCount = 0; }
               {
               		sqlist=new ArrayList();
					Specifier tspec=null;
					Specifier tqual=null;
				}
        :       (               options {   // this loop properly aborts when
                                            // it finds a non-typedefName ID MBZ
                                            warnWhenFollowAmbig = false;
                                        } :
                /* A type : BaseType */
( "struct" | "union" | "enum" | typeSpecifier )=>
                ( typeSpecifier )=>
                  tspec = typeSpecifier {sqlist.add(tspec);}
                | 
                /* A Modifier : int value */
                tqual=typeQualifier {sqlist.add(tqual);}
                )+
        ;

/*
 * List of Declarators
 */ 
structDeclaratorList returns [List sdlist]
				{
					sdlist = new ArrayList();
         			Declarator sdecl=null;
         		}
        :       sdecl = structDeclarator
        		{
        			/*
        			 * why am I getting a null value here ?
        			 */
        			if(sdecl != null)
        			sdlist.add(sdecl);
        		} 
        		( options{warnWhenFollowAmbig=false;}: 
        		COMMA! sdecl=structDeclarator 
        		{
        			sdlist.add(sdecl);
        		}
        		)*
        ;
		
/*
 *	Declarator
 */ 
structDeclarator returns [Declarator sdecl]
		{
			sdecl=null; 
			Expression expr1=null;
		}
        :       ( sdecl = declarator )?
// OM:
//                ( COLON expr1=constExpr )?
                /*
                 * This needs to be fixed
                 */
                //{sdecl.addExpr(expr1);}
            	// Ignore this GCC dialect
            	/*
            	{if(sdecl == null && expr1 == null){
            	System.err.println("Errorororororo");
            	}
            	}*/
// OM:
//                ( attributeDecl )*
        ;

/*
 * UserSpecifier (Enumuration)
 */ 
enumSpecifier returns[Specifier spec]
		 {
		 	Enumeration espec = null; 
		 	String enumN = null;
		 	List elist=null;
		 	spec = null;
		 }
        :       "enum"^
                ( ( ID LCURLY )=> i:ID
                LCURLY elist=enumList RCURLY
                 {enumN =i.getText();}
                | el1:LCURLY elist=enumList RCURLY
                	//{enumN = "anonymous";}
                	//{enumN = "";}
                	{
                	
                	enumN = getLexer().originalSource +"_"+ ((CToken)el1).getTokenNumber();
                		enumN =enumN.replaceAll("[.]","_");
                		enumN =enumN.replaceAll("-","_");
                	}
                | espec2:ID {enumN =espec2.getText();}
                )
				// has name and list of members
                {
                	if(elist != null){
                	
                		espec = new Enumeration(new Identifier(enumN),elist);
                		{
                    		symtab.addDeclaration(espec);
                    	}
                	}
                	
                	
                	spec = new UserSpecifier(new Identifier("enum "+enumN));
                }
        ;
/*
 * List of Declarator
 */
         
enumList returns [List elist]
         {  
         	Declarator enum1=null; 
         	elist = new ArrayList();
         }
        :       enum1=enumerator {elist.add(enum1);}
        		( options{warnWhenFollowAmbig=false;}: 
        		COMMA! enum1=enumerator {elist.add(enum1);}
        		)* 
        		( COMMA! )?
        ;

/*
 *	Declarator
 */
// Complicated due to setting values for each enum value 
enumerator  returns[Declarator decl]
        {
        	decl=null;Expression expr2=null;
        	
        	String val = null;
        }
        :       /*
        		 * Declarator
        		 */
        		i:ID {
        			val = i.getText();
        			decl = new Declarator(new Identifier(val));
        		}
        		/*
        		 * Initializer               
        		 */
                (ASSIGN expr2=constExpr 
                 {
        			decl.setInitializer(new Initializer(expr2));
        		}
                
                )?
               
        ;

// Not handling this as of now (sort of GCC stuff)
attributeDecl
        :       "__attribute"^ LPAREN LPAREN attributeList RPAREN RPAREN
                | "asm"^ LPAREN stringConst RPAREN 
        ;

attributeList
        :       attribute ( options{warnWhenFollowAmbig=false;}: COMMA attribute)*  ( COMMA )?
        ;

attribute
        :       ( ~(LPAREN | RPAREN | COMMA)
                |  LPAREN attributeList RPAREN
                )*
        ;

/*
 *	List of Declarator
 */
initDeclList returns [List dlist]
        		{
	        		Declarator decl=null; 
					dlist = new ArrayList();
        		}
        :       decl = initDecl
        		{
	        		dlist.add(decl);
	    		} 
                ( options{warnWhenFollowAmbig=false;}: 
                COMMA! 
                decl = initDecl
                {
	        		dlist.add(decl);
	    		}  
                )*
                ( COMMA! )?
        ;
/*
 *	Declarator
 */
initDecl returns [Declarator decl]
                {
					decl = null;
					//Initializer binit=null;
					Object binit = null;
					Expression expr1=null;
				}
        :       
        		// casting could cause a problem
        		decl = declarator
                ( attributeDecl )* // Not Handled
                ( ASSIGN binit=initializer
                | COLON expr1=expr // What is this guy ?
                )?
                {
                	if(binit instanceof Expression)
                		binit = new Initializer((Expression)binit);
                	decl.setInitializer((Initializer)binit);
                }
        ;


// add a pointer to the type list 
pointerGroup returns [List bp]
         {
         	bp = new ArrayList(1); 
         	Specifier temp = null;
         	boolean b_const = false;
         	boolean b_volatile = false;
         }
	        
        :       ( 
        			STAR 
        			 // add the modifer
        			(
        				temp = typeQualifier 
        				{
        					if(temp == Specifier.CONST)
        						b_const = true;
        					
        					else if(temp == Specifier.VOLATILE)
        						b_volatile = true;
        				}
        			)*
        			{
        				if(b_const && b_volatile)
        					bp.add(PointerSpecifier.CONST_VOLATILE);
        				else if(b_const)
        					bp.add(PointerSpecifier.CONST);
        				else if(b_volatile)
        					bp.add(PointerSpecifier.VOLATILE);
        				else {
        					bp.add(PointerSpecifier.UNQUALIFIED);
                        }
        			b_const = false;
        			b_volatile = false;
        			}
        		)+    
        		
        ;

// need to decide what to add
idList returns [List ilist]
         { 
         	int i = 1;
         	String name;
         	ilist = new ArrayList();
         }
        :       idl1:ID
        		{
        			name = idl1.getText();
        			ilist.add(new VariableDeclaration(new Declarator(new Identifier(name))));
        			
        		} 
        		( options{warnWhenFollowAmbig=false;}: COMMA 
        		idl2:ID 
        		{
        				name = idl2.getText();
        				ilist.add(new VariableDeclaration(new Declarator(new Identifier(name))));
        		}
        		)*
        ;

//initializer returns [Initializer binit]
initializer returns [Object binit]
		{binit = null; Expression expr1 = null;
           	List ilist = null;}
        : ( 
        	( 
// OM:        	
//        		( (initializerElementLabel)=> initializerElementLabel )?
                ( 
                	expr1=assignExpr 
                	{ 
                		//binit = new Initializer(expr1);
                		binit = expr1;
                	}
// OM: next option does the same                	
//                	| ilist=lcurlyInitializer
//                	{binit = new Initializer(ilist);} 
                )  
           )
              | ilist=lcurlyInitializer
              	{binit = new Initializer(ilist);}
         )
        ;

// GCC allows more specific initializers
initializerElementLabel {Expression expr1 = null,expr2=null;}
        :   (   ( LBRACKET 
        		((expr1=constExpr VARARGS)=> 
        			expr1=rangeExpr 
        		| expr2=constExpr) RBRACKET (ASSIGN)? )
                | ID COLON
                | DOT ID ASSIGN
            )
        ;

// GCC allows empty initializer lists
lcurlyInitializer returns [List ilist] {ilist = new ArrayList();}
        :  
                LCURLY^ 
                (ilist=initializerList ( COMMA! )? )? 
                RCURLY
        ;
    
initializerList returns [List ilist]
		{Object init = null; ilist = new ArrayList();}
        :       
        		(
        			init = initializer {ilist.add(init);} 
        		) 
        		( 
        				 options{warnWhenFollowAmbig=false;}:COMMA! init = initializer 
        				 {ilist.add(init);}
        		)*
        ;
    
/*
 *	Declarator
 */
declarator returns [Declarator decl]	
			{
				Expression expr1=null;
				String declName = null;
				decl = null;
				Declarator tdecl = null;
				IDExpression idex = null;
				List plist = null;
				List bp = null;
				Specifier aspec = null;
				boolean isArraySpec = false;
				boolean isNested = false;
				List llist = new ArrayList(1);
				List tlist = null;
			}
        :		


        		// Pass "Type" to add pointer Type  
                ( bp=pointerGroup )?   
                {/*
                	if(bp == null)
                		bp = new ArrayList();
                */
                }            
				(attributeDecl)? // For cygwin support
                ( 
                	id:ID 
                	// Add the name of the Var
                	{ 
                		declName = id.getText(); 
                		idex = new Identifier(declName);
						if(hastypedef){
							typetable.put(declName,"typedef");
						}
                	}
                |
                    /*
                     * SchemaVariableProgramVariable
                    */
                    // OM:
                    idex=variableSV                	
                | 
                	/*
                	 *	Nested Declarator
                	 */ 
                	LPAREN
                	tdecl = declarator
                	RPAREN
                	{
	               	}
                )
				/*
				 *	I give up this part !!!
				 */
                (
                	/*
                	 *	Parameter List
                	 */ 
                	plist = declaratorParamaterList
                	{
                		//decl = new Declarator(bp,idex,plist,null,null);
                	}
                | 
                	/*
                	 *	ArraySpecifier
                	 */
                	LBRACKET ( expr1=expr )? RBRACKET 
                	{
                		isArraySpec = true;
                		      			
                			llist.add(expr1);
                		
                	}
                )*
                {
					/*
					 * Possible combinations
					 * []+ ,  ()
					 */
					 if(plist != null){
					    
                		/*
                		if(isArraySpec){
                			
                			aspec = new ArraySpecifier(llist);
                		//aspec = new ArraySpecifier();
                		tlist = new ArrayList();
                		tlist.add(aspec);
                		}
                		*/
                		/*
                		 * ()
                		 */
                		
					}
					else{
						/*
						 * []+
						 */
						
					
						if(isArraySpec){
							/*
							 * []+
							 */
							aspec = new ArraySpecifier(llist);
							//aspec = new ArraySpecifier();
							tlist = new ArrayList();
							tlist.add(aspec);
						}
						
					}
					/*
				if(idex != null){
					decl = new Declarator(bp, idex, plist, tlist,null) ;	
				}
				else{
					// this is wrong
					decl = new Declarator(bp, tdecl, plist) ;
				}
					*/
					
					decl = new Declarator(bp, idex,tdecl,plist, tlist);
 
                }
        ;
/*
 *	List
 */
declaratorParamaterList returns [List plist]
						
        {	
        	plist = new ArrayList();
        }
        :
                LPAREN^ 
                (                           
                        (declSpecifiers)=> 
                        plist=parameterTypeList
                         
                        | (plist=idList)?
                )
                  
                ( COMMA! )?
                RPAREN       
        ;
/*
 *	List of (?)
 */           
parameterTypeList returns [List ptlist]
        { 
        	ptlist = new ArrayList();
        	Declaration pdecl = null;
	    }
        :       pdecl=parameterDeclaration
        		{ptlist.add(pdecl);}
                (   options {
                            warnWhenFollowAmbig = false;
                        } : 
                  ( COMMA | SEMI )  
                  pdecl = parameterDeclaration
                   {ptlist.add(pdecl);}
                )*
                /*
                 *	What about "..." ?
                 */
// OM:
/*                 
                ( ( COMMA | SEMI ) 
                  VARARGS {ptlist.add(new VariableDeclaration(new Declarator(new Identifier("..."))));} 
                )?
*/                
        ;

/*
 *	Declaration (?)
 */
parameterDeclaration returns [Declaration pdecl]
			{	
				pdecl =null;
				List dspec = null;
				Declarator decl = null;
			}
        :       dspec=declSpecifiers
                ( 
                	( declarator )=> decl = declarator
                | 
                	decl = nonemptyAbstractDeclarator
                )?
                {
                	if(decl != null){
                	
                		pdecl = new VariableDeclaration(dspec,decl);
                		if(isFuncDef){
                			currproc.add(pdecl);
                		}
                	}
                	else
                		pdecl = new VariableDeclaration(dspec,new Declarator(new Identifier("")));
                }
        ;

/* JTC:
 * This handles both new and old style functions.
 * see declarator rule to see differences in parameters
 * and here (declaration SEMI)* is the param type decls for the
 * old style.  may want to do some checking to check for illegal
 * combinations (but I assume all parsed code will be legal?)
 */

functionDef returns [Procedure curFunc]
			{
				CompoundStatement stmt=null;
				Declaration decl=null;
				Declarator bdecl=null;
				List dspec=null;
				curFunc = null;
				String declName=null;
				int dcount = 0;
				SymbolTable prev_symtab =null;
				SymbolTable temp_symtab = new CompoundStatement();
			}
                           
        :       ( 
        		{ isFuncDef = true;}
        		(functionDeclSpecifiers)=> 
        		dspec=functionDeclSpecifiers
                |  //epsilon
                )
                {
                	if(dspec == null)
                		dspec = new ArrayList();
                } 
                bdecl = declarator
                /*
                 *	This type of declaration is a problem
                 */
                 {
                 		prev_symtab = symtab;
                 		symtab = temp_symtab; 
                 		old_style_func = true;
                 		func_decl_list.clear();
                 }
                ( declaration {dcount++;})* (VARARGS)? ( SEMI! )*
                {
                	old_style_func = false;
                	symtab = prev_symtab;
                }
                {
                
                	isFuncDef = false;
                
                	if(dcount > 0){
                		HashMap hm = null;
                		ListIterator i = ((ArrayList)(bdecl.getParameters())).listIterator();
					    Identifier name = null;
					    Declaration tdecl = null;
					    while (i.hasNext())
					    {
					      VariableDeclaration vdec = (VariableDeclaration)i.next();
					
					      Iterator j = vdec.getDeclaredSymbols().iterator();
					      while (j.hasNext())
					      {
					      	// declarator name
					        name = (Identifier)(j.next());
					       /* 
					        // find matching Declaration
					        
					        hm = temp_symtab.getTable();
					        
					        tdecl = (Declaration)(hm.get(name));
					        if(tdecl == null){
					        	//ByteArrayOutputStream bs = new ByteArrayOutputStream(); 
					        	//name.print(bs);
					        	System.err.println("cannot find symbol "+name+"------------"+hm);
					        }
					        	
					        // replace declaration
					        else
					        i.set(tdecl);
					        */
					        
					        // find matching Declaration
					        
					        tdecl = (Declaration)(func_decl_list.get(name.toString()));
					        if(tdecl == null){
					        	//ByteArrayOutputStream bs = new ByteArrayOutputStream(); 
					        	//name.print(bs);
					        	System.err.println("cannot find symbol "+name+ "in old style function declaration, now assuming an int");
					        	tdecl = new VariableDeclaration(Specifier.INT,new Declarator(name)) ;
					        	i.set(tdecl);
					        }
					        // replace declaration
					        else
					        i.set(tdecl);
					        
					      }
					    }
                
                		Iterator diter = temp_symtab.getTable().entrySet().iterator();
	                	Object tobject = null;
	                	while(diter.hasNext()){
	                		tobject = diter.next(); 
	                		if(tobject instanceof Annotation)
	                			symtab.addDeclaration((Declaration)tobject); 
	                	}
	                }
                	
                
				}
                stmt=compoundStatement
                {
					if(stmt != null){
						curFunc = new Procedure(dspec,bdecl, stmt);
					}
					// function delaration
					else{
						curFunc = new Procedure(dspec,bdecl, stmt);
					}
					// already handled in constructor
					/*
					Iterator iter = currproc.iterator();
					while(iter.hasNext()){
						curFunc.addDeclaration((Declaration)(iter.next()));
					}
					*/
					//System.err.println(currproc);
					currproc.clear();
				}
        ;

functionDeclSpecifiers returns [List dspec]
         {
         	dspec = new ArrayList();
         	Specifier type=null;
         	Specifier tqual=null;
         	Specifier tspec=null;
         }
        :       ( options {   // this loop properly aborts when
                   // it finds a non-typedefName ID MBZ
                  warnWhenFollowAmbig = false;
                  } :
                  type=functionStorageClassSpecifier {dspec.add(type);}
                | tqual=typeQualifier {dspec.add(tqual);}
                | ( "struct" | "union" | "enum" | tspec=typeSpecifier)=>                
                        tspec=typeSpecifier {dspec.add(tspec);}
                )+
        ;

declarationList [CompoundStatement cstmt]
			{Declaration decl=null;ArrayList tlist = new ArrayList();}
         :       (               options {   // this loop properly aborts when
                                            // it finds a non-typedefName ID MBZ
                                            warnWhenFollowAmbig = false;
                                        } :
    
                localLabelDeclaration
                |  ( declarationPredictor )=> 
                	decl=declaration //{ if(decl != null ) tlist.add(0,decl);}
                	{ if(decl != null ) cstmt.addDeclaration(decl);}	
                )+
                /*
                {
                	int i = 0;
                	for(i = 0; i < tlist.size();i++){
                		cstmt.addDeclaration((Declaration)tlist.get(i));
                	}
                }*/
        ;

declarationPredictor  {Declaration decl=null;}
        :       (options {      //only want to look at declaration if I don't see typedef
                    warnWhenFollowAmbig = false;
                }:
                "typedef"
                | decl=declaration
                )
        ;
        
localLabelDeclaration    
        :       ( //GNU note:  any __label__ declarations must come before regular declarations.
// OM: (SEMI!)+        
                "__label__"^ ID (options{warnWhenFollowAmbig=false;}: COMMA! ID)* ( COMMA! )? ( SEMI! )
                )
        ;

// OM:
codeBlock returns [CompoundStatement stmt]  {
            stmt = null;
        }
        :
            CONTEXTSTART 
            {
                stmt = new ContextFrame();
                stmt.setLineNumber(LT(1).getLine());
                symtab = stmt;
            }
            statementDeclarationList[stmt]
            CONTEXTEND
        |
            {
                stmt = new RootFrame();
                stmt.setLineNumber(LT(1).getLine());
                symtab = stmt;
            }
            statementDeclarationList[stmt]
        ;

compoundStatement returns [CompoundStatement stmt]{
				stmt = null;
                int linenum = 0;
				
				SymbolTable prev_symtab = symtab;
                //System.out.println("SchemaCParser::compoundStatement ==> ");
				}
        :       lcur:LCURLY^ {linenum = lcur.getLine();}
                 {
                    	stmt = new CompoundStatement();
                    	stmt.setLineNumber(linenum);
                    	putPragma(lcur,prev_symtab);
                    	symtab = stmt;
                    }

	            statementDeclarationList[stmt]               
	            
                rcur:RCURLY 
                {
                	linenum = rcur.getLine();
                   	putPragma(rcur,stmt);
                    symtab = prev_symtab;
                }
        ;

//Not handled now
nestedFunctionDef 
                            { Declarator decl=null; }
        :       ( "auto" )? //only for nested functions
                ( (functionDeclSpecifiers)=> functionDeclSpecifiers
                )?
                // "null" could cause a problem
                decl = declarator
                ( declaration )*
                compoundStatement
        ;

// OM:
statementDeclarationList [CompoundStatement cstmt] 
	{
		Declaration decl;
	}
 :	
 			(
 				// TODO: labels!
					( declarationPredictor ) => decl = declaration
                	{ if(decl != null ) cstmt.addStatement(new DeclarationStatement(decl));}	
            	|
                	statement[cstmt]
            )*
        ;

statementList [CompoundStatement cstmt]{
				//System.out.println("SchemaCParser::statementList ==> ");
		}
        :        ( statement[cstmt] )+
        ;

statement	[CompoundStatement cstmt] returns [Statement statb] 
		{ Expression stmtb_expr;
			statb = null;
			Expression expr1=null, expr2=null, expr3=null;
	         Statement stmt1=null,stmt2=null;
	         int a=0;
	         int sline = 0;
	        
	         if(cstmt == null){
	         	cstmt = new CompoundStatement();
	         }
            //System.out.println("SchemaCParser::statement ==> ");
            
            // OM:
            List metaArguments;
		}
        :       
        		/*
        		 *	NullStatement
        		 */
        		tsemi:SEMI                    // Empty statements
        		{
        			sline = tsemi.getLine();
        			statb = new NullStatement();
        			putPragma(tsemi,cstmt);
        			cstmt.addStatement(statb);
        		}
        |       
        		/*
        		 * CompoundStatement
        		 */
        		statb=compoundStatement      // Group of statements
        		{cstmt.addStatement(statb);}
        |  
        		/*
        		 * ExpressionStatement
        		 */ 	    
        		// OM: no test
        		//(expr SEMI!)=> 
        		stmtb_expr=expr exprsemi:SEMI!
        		{
                    sline = exprsemi.getLine();
        			putPragma(exprsemi,cstmt);
        			/*
        			 *	I really shouldn't do this test
        			 */
        			
        			statb = new ExpressionStatement(stmtb_expr);
        			cstmt.addStatement(statb);
        		}
// Iteration statements:
        |   
        		/*
        		 * WhileLoop
        		 */
        	    twhile:"while"^ LPAREN!
        		{
        			sline = twhile.getLine();
        			putPragma(twhile,cstmt);
        		} 
        		expr1=expr RPAREN! stmt1=statement[null]
        		{
					statb = new WhileLoop(expr1, stmt1);
					statb.setLineNumber(sline);
					
        			
        			cstmt.addStatement(statb);
				}
        |       
        		/*
        		 * DoLoop
        		 */ 
        		tdo:"do"^ 
        		{
        			sline = tdo.getLine();
        			putPragma(tdo,cstmt);
        		}
        		stmt1=statement[null] "while"! LPAREN! 
        		expr1=expr RPAREN! SEMI!
        		{
        			statb = new DoLoop(stmt1, expr1);
					statb.setLineNumber(sline);
					
        			cstmt.addStatement(statb);
        		}
        |		/*
        		 * ForLoop
        		 */
        
        	!      tfor:"for"
        		{
        			sline = tfor.getLine();
        			putPragma(tfor,cstmt);
        		 
        		}
                LPAREN ( expr1=expr )? //{if (expr1 == null) expr1 = new Expression();} 
                SEMI ( expr2=expr )? //{if (expr2 == null) expr2 = new Expression();}
                SEMI ( expr3=expr )? //{if (expr3 == null) expr3 = new Expression();}
                RPAREN
                stmt1=statement[null]
				{  	if(expr1 != null)
					statb = new ForLoop(new ExpressionStatement(expr1),expr2,expr3,stmt1);
                	else
                	statb = new ForLoop(new NullStatement(),expr2,expr3,stmt1);
                	statb.setLineNumber(sline);
                
        			cstmt.addStatement(statb);
        		}
// Jump statements:
        |       
        		/*
        		 * GotoStatement
        		 */
        		tgoto:"goto"^
        		{
        			sline = tgoto.getLine();
        			putPragma(tgoto,cstmt);
        		} 
        		//expr1=expr SEMI!
        		gotoTarget:ID SEMI!
        		{
        			/*
        			BaseDeclaration target = null;
        			Object o = null;
        			o =functionSymtab.get(gotoTarget.getText());
        			if(o == null){
        				target = new BaseDeclaration(new BaseSpecifier(),null);
        				functionSymtab.put(gotoTarget.getText(),target);
        			}
        			else
        				target = (Declaration)o;
        				
        			statb = new GotoStmt(target);
        			*/
        			statb = new GotoStatement(new Identifier(gotoTarget.getText()));
        			
        			statb.setLineNumber(sline);
        		
        			cstmt.addStatement(statb);
        		}
        			
        |       
        		/*
        		 * ContinueStatement
        		 */
        		tcontinue:"continue" SEMI!
        		{	
        			sline = tcontinue.getLine();
        			 
        			statb = new ContinueStatement();
        			statb.setLineNumber(sline);
        			putPragma(tcontinue,cstmt);
        			cstmt.addStatement(statb);
        		}
        		
        |       
        		/*
        		 *	BreakStatement
        		 */
        		tbreak:"break" SEMI!
        		{	
        			sline = tbreak.getLine();
        			
        			statb = new BreakStatement();
        			statb.setLineNumber(sline);
        			putPragma(tbreak,cstmt);
        			cstmt.addStatement(statb);
        		}
        		
        |       
        		/*
        		 *	ReturnStatement
        		 */
        		treturn:"return"^ 
        		{	
        			sline = treturn.getLine();
        			
        		}
        		( expr1=expr )? SEMI!
        		{ 
        			if(expr1 != null)
        				statb=new ReturnStatement(expr1);
        			else
        				statb=new ReturnStatement();
        			statb.setLineNumber(sline);
        			putPragma(treturn,cstmt);
        			cstmt.addStatement(statb);
        		}
        |       
        		/*
        		 * Label
        		 */
        		lid:ID COLON! 
        		{
        			sline = lid.getLine();
        			
        		}
        		{ 
        			Object o = null;
        			Declaration target = null;
        			statb = new CompoundStatement();
        			//statb = new Label(new Identifier(lid.getText()));
					((CompoundStatement)statb).addStatement(new Label(new Identifier(lid.getText())));
					/*
					o = functionSymtab.get(lid.getText());
					// place holder is there
					if(o != null){
						target = (Declaration)o;
						target.getSpecifier().add(statb);
					}
					else{
						Specifier spec = new Specifier();
						spec.add(statb);
						target = new Declaration(spec,null);
						functionSymtab.put(lid.getText(),target);
					}
					*/
					statb.setLineNumber(sline);
				putPragma(lid,cstmt);
        			cstmt.addStatement(statb);
        		}
        		(options {warnWhenFollowAmbig=false;}: stmt1=statement[cstmt] {((CompoundStatement)statb).addStatement(stmt1);})?  
        		
// GNU allows range expressions in case statements
        |       
        		/*
        		 *	Case
        		 */
        		tcase:"case"^ 
        		{
        			sline = tcase.getLine();
        		
        		}
        		((constExpr VARARGS)=> 
        			expr1=rangeExpr 
        			| expr1=constExpr) 
        		
        		{ 
        			statb = new Case(expr1);
					statb.setLineNumber(sline);
					putPragma(tcase,cstmt);
        			cstmt.addStatement(statb);
        		}
        		COLON! ( options{warnWhenFollowAmbig=false;}:
        		stmt1=statement[cstmt] )?
        		
        |       
        		/*
        		 * Default
        		 */
        		tdefault:"default"^ 
        		{
        			sline = tdefault.getLine(); 
        		}
        		
        		{ 
        			statb = new Default();
					statb.setLineNumber(sline);
					putPragma(tdefault,cstmt);
        			cstmt.addStatement(statb);
        		}
        		COLON! ( options{warnWhenFollowAmbig=false;}: 
        		stmt1=statement[cstmt] )?

// Selection statements:

        |       /*
         		 * IfStatement;
         		 */
        		tif:"if"^
        		{
        			sline = tif.getLine();
        			putPragma(tif,cstmt);
        		}
                 LPAREN! expr1=expr RPAREN! stmt1=statement[null]  
                ( //standard if-else ambiguity
                        options {
                            warnWhenFollowAmbig = false;
                        } :
                "else" stmt2=statement[null] )?
                 {
		 			if(stmt2 != null)
			 			statb = new IfStatement(expr1,stmt1,stmt2);
			 		else
			 			statb = new IfStatement(expr1,stmt1);
			 		statb.setLineNumber(sline);
			 	
        			cstmt.addStatement(statb);
		 		}
        |       
        		/*
        		 *	SwitchStatement
        		 */
        		tswitch:"switch"^ LPAREN! 
        		{
        			sline = tswitch.getLine();
        		 }
        		expr1=expr RPAREN! 
        		{ 
        			statb = new SwitchStatement(expr1);
					statb.setLineNumber(sline);
				putPragma(tswitch,cstmt);
        			cstmt.addStatement(statb);
        		}
        		stmt1=statement[null]{
        			((SwitchStatement)statb).setBody((CompoundStatement)stmt1);
        		}
        |
                /*
                 * SchemaVariableStatement
                 */
                // OM: disambiguation
                 (statementSV) =>
                statb=statementSV
                {cstmt.addStatement(statb);}
        |
        		// OM:
        	    tallocate:"allocate"^
        		{	
        			sline = tallocate.getLine();
        		}        	    
        	    expr1=expr SEMI! 
        		{
      				statb=new AllocateStatement(expr1);
        			statb.setLineNumber(sline);
        			putPragma(tallocate,cstmt);
        			cstmt.addStatement(statb);
        		}
        |
        		// OM:
        	    tdestroy:"destroy"^ 
        		{	
        			sline = tdestroy.getLine();
        			
        		}
    	    	expr1=expr SEMI! 
        		{ 
      				statb=new DestroyStatement(expr1);
        			statb.setLineNumber(sline);
        			putPragma(tdestroy,cstmt);
        			cstmt.addStatement(statb);
        		}
        |
        		// OM:
        	    tstmntmeta:META_STATEMENT_PREFIX
        		{	
        			sline = tstmntmeta.getLine();        			
        		}        	    
				svID:SCHEMA_ID LPAREN
				metaArguments = metaArguments
				RPAREN SEMI!
        		{ 
      				statb=new MetaStatement(svID.getText(), metaArguments);
        			statb.setLineNumber(sline);
        			putPragma(tstmntmeta,cstmt);
        			cstmt.addStatement(statb);
        		}
        ;

statementSV returns [StatementSVWrapper svStmt]
    {
        svStmt = null;
    }
    :
   	    { strategy.testStatementSV( LT(1).getText() )  }?
        svID:SCHEMA_ID
        {
            try {
                svStmt = strategy.getStatementSV(svID.getText());
            } catch(ParserStrategy.NotFoundException e) {
            	throw new RuntimeException(e);
        	}
        }
        exception
          catch [SemanticException ex] {
            throw new NoViableAltException(LT(1), getFilename());
        };





expr	returns [Expression ret_expr] 
{ret_expr = null; Expression expr1=null,expr2=null; List elist = new ArrayList();
    //System.out.println("SchemaCParser::expr ==> ");
	}
        :
                ret_expr=assignExpr 
        		{
                           	elist.add(ret_expr);
                }
        		(options {
                                /* MBZ:
                                    COMMA is ambiguous between comma expressions and
                                    argument lists.  argExprList should get priority,
                                    and it does by being deeper in the expr rule tree
                                    and using (COMMA assignExpr)*
                                */
                                warnWhenFollowAmbig = false;
                            } :
                            /*
                             * CommaExpression is not handled now
                             */
                            
                            c:COMMA^ 
                           
                            expr1=assignExpr  
                            {elist.add(expr1);
                            }
                            )*
                            {
                            
                            	if(elist.size() > 1){
                            		//System.err.println("CommaExpr");
                            		ret_expr = new CommaExpression(elist);
                            	}
                            }
        ;




expressionSV returns [ExpressionSVWrapper svExpr]
    {
        svExpr = null;
    }
    :
	    { strategy.testExpressionSV( LT(1).getText() )  }?
        svID:SCHEMA_ID
        {
        	try {
	            svExpr = strategy.getExpressionSV(svID.getText());
	        }
	        catch(ParserStrategy.NotFoundException e) {
	        	throw new RuntimeException(e);
	        }
        }
        exception
          catch [SemanticException ex] {
            throw new NoViableAltException(LT(1), getFilename());
        };        

assignExpr returns [Expression ret_expr] 
			{ ret_expr = null; Expression expr1=null;AssignmentOperator code=null;}
        :       //(ret_expr=conditionalExpr | ret_expr=programVariableSV) 
                ret_expr=conditionalExpr
                // OM:
                (
        		( code = assignOperator!         		 
                    //(expr1=expressionSV | expr1=assignExpr)
                    expr1=assignExpr
        		{ret_expr = new AssignmentExpression(ret_expr,code,expr1); } 
        		)
        		|
        		(
	        		REF_ASSIGN
					expr1=assignExpr
					{ret_expr = new ReferenceAssignmentExpression(ret_expr, expr1); }   		
        		)
        		)?
        ;	
  

assignOperator returns [AssignmentOperator code] {code = null;}
        :       ASSIGN 				{code = AssignmentOperator.NORMAL;}       
        |       DIV_ASSIGN          {code = AssignmentOperator.DIVIDE;}  
        |       PLUS_ASSIGN         {code = AssignmentOperator.ADD;} 
        |       MINUS_ASSIGN        {code = AssignmentOperator.SUBTRACT;} 
        |       STAR_ASSIGN         {code = AssignmentOperator.MULTIPLY;} 
        |       MOD_ASSIGN          {code = AssignmentOperator.MODULUS;}    
        |       RSHIFT_ASSIGN       {code = AssignmentOperator.SHIFT_RIGHT;} 
        |       LSHIFT_ASSIGN       {code = AssignmentOperator.SHIFT_LEFT;} 
        |       BAND_ASSIGN         {code = AssignmentOperator.BITWISE_AND;} 
        |       BOR_ASSIGN          {code = AssignmentOperator.BITWISE_INCLUSIVE_OR;} 
        |       BXOR_ASSIGN         {code = AssignmentOperator.BITWISE_EXCLUSIVE_OR;} 
        ;

constExpr returns [Expression ret_expr] {ret_expr = null;}
        :       ret_expr=conditionalExpr
        ;

logicalOrExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=logicalAndExpr 
        		( LOR^ expr1=logicalAndExpr
        		{ret_expr = new BinaryExpression(ret_expr,BinaryOperator.LOGICAL_OR,expr1);} 
        		)*
        ;


logicalAndExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=inclusiveOrExpr 
        		( LAND^ expr1=inclusiveOrExpr 
        		{ret_expr = new BinaryExpression(ret_expr,BinaryOperator.LOGICAL_AND,expr1);}
        		)*
        ;

inclusiveOrExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=exclusiveOrExpr 
        		( BOR^  expr1=exclusiveOrExpr 
        		{ret_expr = new BinaryExpression(ret_expr,BinaryOperator.BITWISE_INCLUSIVE_OR,expr1);} 
        		)*
        ;


exclusiveOrExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=bitAndExpr 
        		( BXOR^  expr1=bitAndExpr 
        		{ret_expr = new BinaryExpression(ret_expr,BinaryOperator.BITWISE_EXCLUSIVE_OR,expr1);} 
        		)*
        ;


bitAndExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=equalityExpr 
        		( BAND^  
        		expr1=equalityExpr
        		{ret_expr = new BinaryExpression(ret_expr,BinaryOperator.BITWISE_AND,expr1);} 
        		)*
        ;



equalityExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=relationalExpr
                ( ( EQUAL^ {code = BinaryOperator.COMPARE_EQ;}
                | NOT_EQUAL^ {code = BinaryOperator.COMPARE_NE;}) 
                 
                expr1=relationalExpr 
                {ret_expr = new BinaryExpression(ret_expr,code,expr1);} 
                )*
        ;


relationalExpr	 returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=shiftExpr
                ( ( LT^ {code = BinaryOperator.COMPARE_LT;}
                | LTE^ {code = BinaryOperator.COMPARE_LE;}
                | GT^ {code = BinaryOperator.COMPARE_GT;}
                | GTE^ {code = BinaryOperator.COMPARE_GE;}) 
                 
                expr1=shiftExpr 
                {ret_expr = new BinaryExpression(ret_expr,code,expr1);} 
                )*
        ;



shiftExpr returns  [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=additiveExpr
                ( ( LSHIFT^ {code = BinaryOperator.SHIFT_LEFT;}
                | RSHIFT^ {code = BinaryOperator.SHIFT_RIGHT;}) 
                
                expr1=additiveExpr
                {ret_expr = new BinaryExpression(ret_expr,code,expr1);}  
                )*
        ;


additiveExpr returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=multExpr
                ( ( PLUS^ {code = BinaryOperator.ADD;} 
                | MINUS^ {code=BinaryOperator.SUBTRACT;}) 
                
                expr1=multExpr
                {ret_expr = new BinaryExpression(ret_expr,code,expr1);} 
                )*
        ;


multExpr	returns [Expression ret_expr]{
				Expression expr1, expr2; ret_expr=null;
				BinaryOperator code = null;
			}
        :       ret_expr=castExpr
                ( ( STAR^ {code = BinaryOperator.MULTIPLY;}
                | DIV^ {code=BinaryOperator.DIVIDE;}
                | MOD^ {code=BinaryOperator.MODULUS;}) 
               
                expr1=castExpr
                 {ret_expr = new BinaryExpression(ret_expr,code,expr1);} 
                )*
        ;




typeName	returns [List tname]
		{
			tname=null;
			
			//Declarator decl= new Declarator();
			Declarator decl = null;
		}
        :       tname = specifierQualifierList 
        		/*
        		 *	Need to add this part
        		 */
        		(decl = nonemptyAbstractDeclarator {tname.add(decl);})?
        ;


postfixExpr  returns [Expression ret_expr]
				{
					ret_expr=null;
					Expression expr1=null;
				} 
        :       expr1=primaryExpr
        		{ret_expr = expr1;}
                (
                ret_expr=postfixSuffix[expr1]
                )?
        ;
postfixSuffix [Expression expr1] returns [Expression ret_expr]
        		{
        			Expression expr2=null;
        			//boolean builtin=false;
        			SymbolTable saveSymtab = null;
        			String s;
					ret_expr = expr1;
					List args = null;
				}
        :
                ( 
                /* 
                 * POINTER_ACCESS
                 * 
                 */
                PTR ptr_id:ID
                {
                	/*
                	ret_expr = 
                	new BinaryExpression(ret_expr,BinaryOperator.POINTER_ACCESS,new Identifier(ptr_id.getText()));
                	*/
                	ret_expr = new AccessExpression(ret_expr,AccessOperator.POINTER_ACCESS,new Identifier(ptr_id.getText()));
                }
                | 
                // OM:
                /* 
                 * Schema POINTER_ACCESS
                 * 
                 */
                PTR expr2 = memberSV
                {
                	ret_expr = 
                	new AccessExpression(ret_expr,AccessOperator.POINTER_ACCESS,expr2);
                }
                | 
                /* 
                 * MEMBER_ACCESS
                 * 
                 */
                DOT dot_id:ID
                {
                	/*
                	ret_expr = 
                	new BinaryExpression(ret_expr,BinaryOperator.MEMBER_ACCESS,new Identifier(dot_id.getText()));
                	*/
                	ret_expr = 
                	new AccessExpression(ret_expr,AccessOperator.MEMBER_ACCESS,new Identifier(dot_id.getText()));
                }
                | 
                // OM:
                /* 
                 * Schema MEMBER_ACCESS
                 * 
                 */
                DOT expr2 = memberSV
                {
                	ret_expr = 
                	new AccessExpression(ret_expr,AccessOperator.MEMBER_ACCESS,expr2);
                }
                /*
                 *	FunctionCall
                 */
                | args=functionCall
                {
                	if(args == null)
                		ret_expr = new FunctionCall(ret_expr);
                	else
                		ret_expr = new FunctionCall(ret_expr,args);
                }	
                /*
                 * ArrayAcess
                 * Need a fix for multi-dimension access
                 */
                | LBRACKET expr2=expr RBRACKET
                {
                	// OM:
                	/*
                	if(ret_expr instanceof ArrayAccess){
                		ArrayAccess aacc = (ArrayAccess)ret_expr;
                		int dim = aacc.getNumIndices();
                		int n = 0;
                		ArrayList alist = new ArrayList();
                		for(n = 0;n < dim; n++){
                		
                			alist.add(aacc.getIndex(n)); 
						}
						alist.add(expr2);
                		aacc.setIndices(alist); 
 
                	}
                	else
                	*/
						ret_expr = new ArrayAccess(ret_expr,expr2);
				}
                | INC {ret_expr = new UnaryExpression(UnaryOperator.POST_INCREMENT,ret_expr);}
                | DEC {ret_expr = new UnaryExpression(UnaryOperator.POST_DECREMENT,ret_expr);}
                 /*
                 | 
                LPAREN^ expr2=assignExpr COMMA parameterDeclaration[null] RPAREN
                {
                	ExprList eList=new ExprList();
               	eList.add(expr2);
                	ret_expr = new FuncExpr(ret_expr,eList);
                	ret_expr.print();
                	}*/
                )+
        ;

functionCall	returns [List args] {
					args=null;
				}
        :
                LPAREN^  (args=argExprList)? RPAREN
        ;


conditionalExpr returns [Expression ret_expr] 
				{ ret_expr=null;
				Expression expr1=null,expr2=null,expr3=null;}
        :       expr1=logicalOrExpr {ret_expr = expr1;}
                ( QUESTION^ (expr2=expr)? COLON expr3=conditionalExpr 
				{	//if(expr2 == null) expr2 = new Expression();
					ret_expr = new ConditionalExpression(expr1,expr2,expr3);}
				)?
        ;

rangeExpr  returns [Expression ret_expr] //used in initializers only
			{ret_expr = null;}
        :  constExpr VARARGS constExpr
        ;

castExpr	returns [Expression ret_expr]
				{
					ret_expr = null;
					Expression expr1=null;
					List tname=null;
				}
        :       ( LPAREN typeName RPAREN )=>
                LPAREN^ tname=typeName RPAREN 
                ( expr1=castExpr
                	{
                		//System.err.println("Typecast");
                		ret_expr = new Typecast(tname,expr1);
                	} 
                | lcurlyInitializer // What is this ? 
                )
        |       ret_expr=unaryExpr
        ;

/*
 *	This causing problems with type casting
 */
nonemptyAbstractDeclarator returns [Declarator adecl]
		{
			Expression expr1=null;
			List plist=null;
			List bp = null;
			boolean empty = true;
			Declarator tdecl = null;
				
			
				Specifier aspec = null;
				boolean isArraySpec = false;
				boolean isNested = false;
				List llist = new ArrayList(1);
				List tlist = null;
				
			adecl = null;
		}
        :   (
                bp = pointerGroup
                (   
                	(LPAREN  
                    (   
                    
                    	(
                    	// ( )
                    	(
                    	tdecl = nonemptyAbstractDeclarator
                        )
                        | 
                        // function proto
                        plist=parameterTypeList 
                       )
                       {empty = false;}
                    )?
                    
                    ( COMMA! )?
                    RPAREN)
                    {
                    
                    if(empty)
                    	plist = new ArrayList();
                    empty = true;
                    }
                | (LBRACKET (expr1=expr)? RBRACKET)
                	{
                		isArraySpec = true;
                		      			
                			llist.add(expr1);
                		
                	}
                )*
            |   (   (LPAREN  
                    (  
                    ( 
                    	// ( )
                    	(
                    	tdecl = nonemptyAbstractDeclarator
                    	)
                        | 
                        // function proto
                        plist=parameterTypeList
                       
                    ) {empty = false;}
                    )?
                    ( COMMA! )?
                    RPAREN)
                    {
                    
                    if(empty)
                    	plist = new ArrayList();
                    empty = true;
                    }
                | (LBRACKET (expr1=expr)? RBRACKET)
                {
                		isArraySpec = true;
                		      			
                			llist.add(expr1);
                		
                	}
                )+
            )
            {
            	// this is wrong
            	/*
            	if(tdecl == null){
					adecl = new Declarator(bp, new Identifier(""), plist, tlist,null) ;	
				}
            	else	
            		adecl = new Declarator(bp, tdecl, plist) ;
            		
            		*/
            		if(isArraySpec){
							/*
							 * []+
							 */
							aspec = new ArraySpecifier(llist);
							//aspec = new ArraySpecifier();
							tlist = new ArrayList();
							tlist.add(aspec);
					}
            		{ Identifier idex = null;
            			
            			if(tdecl == null)
            				idex = new Identifier("");
            			
            				adecl = new Declarator(bp, idex,tdecl, plist, tlist);
            		}
            	
            }
        ;

unaryExpr returns [Expression ret_expr]
				{
					Expression expr1=null;
					UnaryOperator code;
					ret_expr = null;
					List tname = null;
				}
        :       ret_expr=postfixExpr
        |       INC^ expr1=castExpr 
        		{ret_expr = new UnaryExpression(UnaryOperator.PRE_INCREMENT, expr1);}
        |       DEC^ expr1=castExpr
        		{ret_expr = new UnaryExpression(UnaryOperator.PRE_DECREMENT, expr1);}
// OM:        		
        |       VALUEOF^ expr1=castExpr
        		{ret_expr = new UnaryExpression(ValueOfOperator.VALUE_OF, expr1);}        		

        |       code=unaryOperator expr1=castExpr 
				{
					ret_expr = new UnaryExpression(code, expr1);
				}
       	/*
       	 *	sizeof is not handled
       	 */
        |       "sizeof"^
                ( ( LPAREN typeName )=> 
                LPAREN tname=typeName RPAREN
                 {ret_expr = new SizeofExpression(tname);}
                | expr1=unaryExpr
                {ret_expr = new SizeofExpression(expr1);}
                )
                /*
                {
                	ByteArrayOutputStream bs = new ByteArrayOutputStream();
                	if(tname != null){
                	
                	Tools.printList(tname,bs);
                	ret_expr = new Identifier("sizeof("+bs.toString() +")");
                	}
                	else {
                		expr1.print(bs);
                		ret_expr = new Identifier("sizeof "+bs.toString());
                	}
                		
                }
                */
        |        // Not ready to handle these attributes
        		"__alignof"^
                ( ( LPAREN typeName )=> 
                	LPAREN tname=typeName RPAREN 
                //	{ret_expr = new UnaryExpression(LITERAL___alignof,tname); } 
                | expr1=unaryExpr 
                //	{ret_expr = new UnaryExpression(LITERAL___alignof,expr1); } 
                )      
        |       gnuAsmExpr {ret_expr = new Identifier("asm");}
        
        ;

unaryOperator returns [UnaryOperator code] {code = null;}
        :       BAND {code = UnaryOperator.ADDRESS_OF;}
        |       STAR {code = UnaryOperator.DEREFERENCE;}
        |       PLUS	{code = UnaryOperator.PLUS;}
        |       MINUS	{code = UnaryOperator.MINUS;}
        |       BNOT	{code = UnaryOperator.BITWISE_COMPLEMENT;}
        |       LNOT	{code = UnaryOperator.LOGICAL_NEGATION;}
//      |       LAND	{code = LAND;}
        |       "__real"	{code = null;}
        |       "__imag"	{code = null;}
        ;

gnuAsmExpr
        :       "asm"^ ("volatile")? 
                LPAREN stringConst
                ( options { warnWhenFollowAmbig = false; }:
                  COLON (strOptExprPair ( COMMA strOptExprPair)* )?
                  ( options { warnWhenFollowAmbig = false; }:
                    COLON (strOptExprPair ( COMMA strOptExprPair)* )?
                  )?
                )?
                ( COLON stringConst ( COMMA stringConst)* )?
                RPAREN
                               // { ##.setType(NGnuAsmExpr); }
        ;

//GCC requires the PARENs
strOptExprPair
        :  stringConst ( LPAREN expr RPAREN )?
        ;


primaryExpr returns [Expression p] {
		Expression expr1=null;
		CompoundStatement cstmt = null;
		p=null;
		String name = null;
		//TNode temp;
            
        // OM:
		List metaArguments;
		}
        :
        //Added by Daniel (for handling of C0)
                "true"
                {
                    p=new BooleanLiteral(true);
                }
        |
                "false"
                {
                    p=new BooleanLiteral(false);
                }
        //
        |
        		/*
        		 *	Identifier
        		 */
        		 prim_id:ID 
        		{
                    //System.out.println("SchemaCParser::primaryExpr ==> prim_id.getText() = " 
                            //+ prim_id.getText());
        			name = prim_id.getText();
 	       			p=new Identifier(name);
        		}
        |       /*
        		 * Need to handle these correctly
        		 */ 
        		prim_num:Number {
        		 	name = prim_num.getText();
        		 	boolean handled = false;
        		 	int i = 0;
        		 	double d = 0;
        		 	Long in = null;
        		 	name = name.toUpperCase();
        		 		name = name.replaceAll("L","");
        		 		name = name.replaceAll("U","");
        		 	 	name= name.replaceAll("I"," ");
        		 	if(name.startsWith("0X") == false){
        		 		name.replaceAll("F","");

        		 	}
        		 	try{
        		 		
        		 		i = Integer.parseInt(name);
        		 		p=new IntegerLiteral(i);
        		 		handled = true; 
        		 	}catch(NumberFormatException e){
        		 		;
        		 	}
        		 	if(handled == false)
        		 	try{d = Double.parseDouble(name);
        		 		p=new FloatLiteral(d);
        		 		handled = true; 
        		 	}catch(NumberFormatException e){
        		 		
        		 		;
        		 	}
        		 	if(handled == false)
        		 	try{ 
        		 		
        		 		
        		 		in = Long.decode(name);
        		 		p=new IntegerLiteral(in.intValue());
        		 	}
        		 	catch(NumberFormatException e){
        		 	
        				p=new Identifier(name);	
        		 		System.err.println("Strange number "+name);
				        // OM:         		 		
				        //System.exit(1);
				        throw new RuntimeException(e);
        		 	}
        		}
        |       name=charConst {
                    //Changed by Daniel
        			//p=new Identifier(name);
                    p=new CharLiteral(name.charAt(1));
                    //
        		}
        |       /*
        		 * StringLiteral
        		 */
        		name=stringConst {
        			//name = name.replaceAll("\"","");	
        			p=new StringLiteral(name);
        			((StringLiteral)p).stripQuotes();
        		}
// JTC:
// ID should catch the enumerator
// leaving it in gives ambiguous err
//      | enumerator
        |       /*
        		 *	Compound statement Expression
        		 */
        		(LPAREN LCURLY) => 
        		LPAREN^ 
        		cstmt = compoundStatement 
        		RPAREN
        		//{ p = new CompoundExpr(cstmt); }
        		//{p = new StringLiteral("CompoundStatement Expression");}
			{
				System.err.println("[DEBUG] Warning: CompoundStatement Expression !");
				ByteArrayOutputStream bs = new ByteArrayOutputStream();
				cstmt.print(bs);
				p = new StringLiteral(bs.toString());
			}
        |       /*
        		 *	Paren
        		 */
        		LPAREN^ expr1=expr RPAREN
        		{
					p=new ParenthesizedExpression(expr1);
				}        
        |
                /*
                 * SchemaVariableExpression
                 */
                p=expressionSV
        |
        		// OM:
        	    META_EXPRESSION_PREFIX svID:SCHEMA_ID LPAREN
				metaArguments = metaArguments
				RPAREN
        		{ 
      				p=new MetaExpression(svID.getText(), metaArguments);
        		}
        ;               

// OM:
variableSV returns [VariableSVWrapper svVar]
    {
        svVar = null;
    }
    :
   	    { strategy.testVariableSV( LT(1).getText() )  }?
        svID:SCHEMA_ID
        {
            try {
                svVar = strategy.getVariableSV(svID.getText());
            } catch(ParserStrategy.NotFoundException e) {
            	throw new RuntimeException(e);
        	}
        }
        exception
          catch [SemanticException ex] {
            throw new NoViableAltException(LT(1), getFilename());
        };        

// OM:
memberSV returns [MemberSVWrapper svMember]
    {
        svMember = null;
    }
    :
   	    { strategy.testMemberSV( LT(1).getText() )  }?
        svID:SCHEMA_ID
        {
            try {
                svMember = strategy.getMemberSV(svID.getText());
            } catch(ParserStrategy.NotFoundException e) {
            	throw new RuntimeException(e);
        	}
        }
        exception
          catch [SemanticException ex] {
            throw new NoViableAltException(LT(1), getFilename());
        };        

/*
 * Type of list is unclear
 */
argExprList  returns [List eList] 
			{
				Expression expr1 = null;
				eList=new ArrayList();
				Declaration pdecl = null;
			}
        :       expr1=assignExpr {eList.add(expr1);}
        		( COMMA! 
        		(
        		 expr1=assignExpr {eList.add(expr1);}
// OM: only in function calls
/*        		 
        		 |
        		 pdecl=parameterDeclaration 
        		 {
        		 	
        		 	eList.add(\*new StringLiteral(pdecl.toString())*\pdecl);
        		 }
*/        		 
        		)
        		)*
        ;


metaArguments returns [List result] 
			{
				de.uka.ilkd.key.logic.op.ProgramSV programSV = null;
				result = new LinkedList();
			}
        :       
        (
	        { strategy.testProgramSV( LT(1).getText() )  }?
        	programSV = programSV { result.add(programSV); }
	        ( 
	        	COMMA!
	        	programSV = programSV { result.add(programSV); }
       		)*
   		)?
        ;
        
programSV returns [de.uka.ilkd.key.logic.op.ProgramSV programSV = null]
		:
        { strategy.testProgramSV( LT(1).getText() )  }?
    	svID:SCHEMA_ID 
    	{ 
    		try {
				programSV = strategy.getProgramSV(svID.getText());
			}
	        catch(ParserStrategy.NotFoundException e) {
	        	throw new RuntimeException(e);
	        }				
		}
		;

protected
charConst	returns [String name] { name = null;}
        :       cl:CharLiteral	{name=cl.getText();}
        ;


protected
stringConst	returns [String name] { name = "";}
        :       (sl:StringLiteral	{name += sl.getText();})+                //{ ## = #(#[NStringSeq], ##); }
        ;


protected
intConst
        :       IntOctalConst
        |       LongOctalConst
        |       UnsignedOctalConst
        |       IntIntConst
        |       LongIntConst
        |       UnsignedIntConst
        |       IntHexConst
        |       LongHexConst
        |       UnsignedHexConst
        ;


protected
floatConst
        :       FloatDoubleConst
        |       DoubleDoubleConst
        |       LongDoubleConst
        ;

dummy
        :       NTypedefName
        |       NInitDecl
        |       NDeclarator
        |       NStructDeclarator
        |       NDeclaration
        |       NCast
        |       NPointerGroup
        |       NExpressionGroup
        |       NFunctionCallArgs
        |       NNonemptyAbstractDeclarator
        |       NInitializer
        |       NStatementExpr
        |       NEmptyExpression
        |       NParameterTypeList
        |       NFunctionDef
        |       NCompoundStatement
        |       NParameterDeclaration
        |       NCommaExpr
        |       NUnaryExpr
        |       NLabel
        |       NPostfixExpr
        |       NRangeExpr
        |       NStringSeq
        |       NInitializerElementLabel
        |       NLcurlyInitializer
        |       NAsmAttribute
        |       NGnuAsmExpr
        |       NTypeMissing
        ;





{
        import java.io.*;
        import antlr.*;
}

class SchemaCLexer extends Lexer;

options
        {
        k = 3;
        exportVocab = SCHEMAC;
        testLiterals = false;
        }
tokens {
        LITERAL___extension__ = "__extension__";
}

{
	public void initialize(String src)
  {
    setOriginalSource(src);
    initialize();
  }

  public void initialize() 
  {
    literals.put(new ANTLRHashString("__alignof__", this), new Integer(LITERAL___alignof));
	literals.put(new ANTLRHashString("__ALIGNOF__", this), new Integer(LITERAL___alignof));
    literals.put(new ANTLRHashString("__asm", this), new Integer(LITERAL_asm));
    literals.put(new ANTLRHashString("__asm__", this), new Integer(LITERAL_asm));
    literals.put(new ANTLRHashString("__attribute__", this), new Integer(LITERAL___attribute));
    
    literals.put(new ANTLRHashString("__complex__", this), new Integer(LITERAL___complex));
    literals.put(new ANTLRHashString("__const", this), new Integer(LITERAL_const));
    literals.put(new ANTLRHashString("__const__", this), new Integer(LITERAL_const));
    literals.put(new ANTLRHashString("__imag__", this), new Integer(LITERAL___imag));
    literals.put(new ANTLRHashString("__inline", this), new Integer(LITERAL_inline));
    literals.put(new ANTLRHashString("__inline__", this), new Integer(LITERAL_inline));
    literals.put(new ANTLRHashString("__real__", this), new Integer(LITERAL___real));
    literals.put(new ANTLRHashString("__restrict", this), new Integer(LITERAL___extension__));
 	literals.put(new ANTLRHashString("__signed", this), new Integer(LITERAL_signed));
    literals.put(new ANTLRHashString("__signed__", this), new Integer(LITERAL_signed));
    literals.put(new ANTLRHashString("__typeof", this), new Integer(LITERAL_typeof));
    literals.put(new ANTLRHashString("__typeof__", this), new Integer(LITERAL_typeof));
    literals.put(new ANTLRHashString("__volatile", this), new Integer(LITERAL_volatile));
    literals.put(new ANTLRHashString("__volatile__", this), new Integer(LITERAL_volatile));
	// MinGW specific
	literals.put(new ANTLRHashString("__MINGW_IMPORT", this), new Integer(LITERAL___extension__));
	literals.put(new ANTLRHashString("_CRTIMP", this), new Integer(LITERAL___extension__));
	// Microsoft specific
	literals.put(new ANTLRHashString("__cdecl", this), new Integer(LITERAL___extension__));
	literals.put(new ANTLRHashString("__w64", this), new Integer(LITERAL___extension__));
	literals.put(new ANTLRHashString("__int64", this), new Integer(LITERAL_int));
	literals.put(new ANTLRHashString("__int32", this), new Integer(LITERAL_int));
	literals.put(new ANTLRHashString("__int16", this), new Integer(LITERAL_int));
	literals.put(new ANTLRHashString("__int8", this), new Integer(LITERAL_int));
  }
  LineObject lineObject = new LineObject();
  String originalSource = "";
  PreprocessorInfoChannel preprocessorInfoChannel = new PreprocessorInfoChannel();
  int tokenNumber = 0;
  boolean countingTokens = true;
  int deferredLineCount = 0;
  int extraLineCount = 1;
  Parser parser = null;
  public void setCountingTokens(boolean ct) 
  {
    countingTokens = ct;
    if ( countingTokens ) {
      tokenNumber = 0;
    }
    else {
      tokenNumber = 1;
    }
  }

    public void setParser(SchemaCParser p){
		parser = p;
	}
 /*
  public void startHeader(String s){
  	//System.out.println(s);
  	parser.startHeader(s);
  }
  public void endHeader(){
  	parser.endHeader();
  }*/
  public void setOriginalSource(String src) 
  {
    originalSource = src;
    lineObject.setSource(src);
  }
  public void setSource(String src) 
  {
    lineObject.setSource(src);
  }
  
  public PreprocessorInfoChannel getPreprocessorInfoChannel() 
  {
    return preprocessorInfoChannel;
  }

  public void setPreprocessingDirective(String pre,int t)
  { 
  /*
  	// handle special pragma cases
  	if(pre.startsWith("#pragma startinclude")){
  		
  		System.out.println("Found "+pre);
  		
  	}
  	else if(pre.startsWith("#pragma endinclude")){
  		System.out.println("Found "+pre); 
    }
    else{
    */
    	//System.out.println("Found "+pre);
    	//preprocessorInfoChannel.addLineForTokenNumber( new Pragma(pre,t), new Integer(lineObject.line) );
    	preprocessorInfoChannel.addLineForTokenNumber( new Pragma(pre,t), new Integer(tokenNumber) );
    /*}*/
  }
  
  protected Token makeToken(int t)
  {
    if ( t != Token.SKIP && countingTokens) {
        tokenNumber++;
    }
    CToken tok = (CToken) super.makeToken(t);
    tok.setLine(lineObject.line);
    tok.setSource(lineObject.source);
    tok.setTokenNumber(tokenNumber);

    lineObject.line += deferredLineCount;
    deferredLineCount = 0;
    return tok;
  }

    public void deferredNewline() { 
        deferredLineCount++;
    }

    public void newline() { 
        lineObject.newline();
        setColumn(1);
    }





}

protected
Vocabulary
        :       '\3'..'\377'
        ;

/* Operators: */

ASSIGN          : '=' ;
COLON           : ':' ;
COMMA           : ',' ;
QUESTION        : '?' ;
SEMI            : ';' ;
PTR             : "->" ;

//Added by Daniel
//SHARP           : '#' ;
CONTEXTSTART    : "..";
CONTEXTEND      : "...";
//


// DOT & VARARGS are commented out since they are generated as part of
// the Number rule below due to some bizarre lexical ambiguity shme.

// DOT  :       '.' ;
protected
DOT:;

// VARARGS      : "..." ;
protected
VARARGS:;


LPAREN          : '(' ;
RPAREN          : ')' ;
LBRACKET        : '[' ;
RBRACKET        : ']' ;
LCURLY          : '{' ;
RCURLY          : '}' ;

EQUAL           : "==" ;
NOT_EQUAL       : "!=" ;
LTE             : "<=" ;
LT              : "<" ;
GTE             : ">=" ;
GT              : ">" ;

DIV             : '/' ;
DIV_ASSIGN      : "/=" ;
PLUS            : '+' ;
PLUS_ASSIGN     : "+=" ;
INC             : "++" ;
MINUS           : '-' ;
MINUS_ASSIGN    : "-=" ;
DEC             : "--" ;
STAR            : '*' ;
STAR_ASSIGN     : "*=" ;
MOD             : '%' ;
MOD_ASSIGN      : "%=" ;
RSHIFT          : ">>" ;
RSHIFT_ASSIGN   : ">>=" ;
LSHIFT          : "<<" ;
LSHIFT_ASSIGN   : "<<=" ;

LAND            : "&&" ;
LNOT            : '!' ;
LOR             : "||" ;

BAND            : '&' ;
BAND_ASSIGN     : "&=" ;
BNOT            : '~' ;
BOR             : '|' ;
BOR_ASSIGN      : "|=" ;
BXOR            : '^' ;
BXOR_ASSIGN     : "^=" ;

// OM:
VALUEOF			: "@";
REF_ASSIGN		: "<-";

Whitespace
        :       ( ( ' ' | '\t' | '\014')
                | "\r\n"                { newline(); }
                | ( '\n' | '\r' )       { newline();    }
                )                       { _ttype = Token.SKIP;  }
        ;


Comment
        :       ("/*"
                ( { LA(2) != '/' }? '*'
                | "\r\n"                { deferredNewline(); }
                | ( '\r' | '\n' )       { deferredNewline();    }
                | ~( '*'| '\r' | '\n' )
                )*
                "*/"
                {setPreprocessingDirective(getText(),Pragma.comment);}
                )                    {

	                						 _ttype = Token.SKIP;
                                        }
        ;


CPPComment
        :
                ("//" ( ~('\n') )* {setPreprocessingDirective(getText(),Pragma.comment);})
                        {

                        _ttype = Token.SKIP;
                        }
        ;

PREPROC_DIRECTIVE
options {
  paraphrase = "a line directive";
}
        :
        '#'
        ( 
        	( "line" || ((Space)+ Digit)) => LineDirective {_ttype = Token.SKIP; }
			| 
			( "pragma" 
				(
					( ~('\n'))* { setPreprocessingDirective(getText(),Pragma.pragma);_ttype = Token.SKIP; }
					| (Space)+ "startinclude" ( ~('\n'))* 
					// {startHeader(getText());} 
					| (Space)+ "endinclude" ( ~('\n'))* {extraLineCount +=2; lineObject.setLine(lineObject.getLine() - 2);}
					// {endHeader();}
				)
			)
			| ( ~('\n'))* {_ttype = Token.SKIP; }                                  
		)
		/*
       
                {
                    _ttype = Token.SKIP;
                }
        */
        ;


protected  Space:
        ( ' ' | '\t' | '\014')
        ;

protected LineDirective
{
        boolean oldCountingTokens = countingTokens;
        countingTokens = false;
}
:
                {
                        lineObject = new LineObject();
                        deferredLineCount = 0;
                }
        ("line")?  //this would be for if the directive started "#line", but not there for GNU directives
        (Space)+
        n:Number { lineObject.setLine(Integer.parseInt(n.getText()) - extraLineCount); }
        (
        (Space)+
        (       fn:StringLiteral {  try {
                                          lineObject.setSource(fn.getText().substring(1,fn.getText().length()-1));
                                    }
                                    catch (StringIndexOutOfBoundsException e) { /*not possible*/ }
                                 }
                | fi:ID { lineObject.setSource(fi.getText()); }
        )?
        (Space)*
        ("1"            { lineObject.setEnteringFile(true); } )?
        (Space)*
        ("2"            { lineObject.setReturningToFile(true); } )?
        (Space)*
        ("3"            { lineObject.setSystemHeader(true); } )?
        (Space)*
        ("4"            { lineObject.setTreatAsC(true); } )?
        (~('\r' | '\n'))*
        //("\r\n" | "\r" | "\n")
        )?
                {
                        //preprocessorInfoChannel.addLineForTokenNumber(new LineObject(lineObject), new Integer(tokenNumber));
                        countingTokens = oldCountingTokens;
                }
        ;



/* Literals: */

/*
 * Note that we do NOT handle tri-graphs nor multi-byte sequences.
 */


/*
 * Note that we can't have empty character constants (even though we
 * can have empty strings :-).
 */
CharLiteral
        :       '\'' ( Escape | ~( '\'' ) ) '\''
        ;


protected BadStringLiteral
        :       // Imaginary token.
        ;


protected
Escape
        :       '\\'
                ( options{warnWhenFollowAmbig=false;}: 
                  ~('0'..'7' | 'x')
                | ('0'..'3') ( options{warnWhenFollowAmbig=false;}: Digit )*
                | ('4'..'7') ( options{warnWhenFollowAmbig=false;}: Digit )*
                | 'x' ( options{warnWhenFollowAmbig=false;}: Digit | 'a'..'f' | 'A'..'F' )+
                )
        ;


/* Numeric Constants: */
protected IntSuffix
        :   'L'
            | 'l'
            | 'U'
            | 'u'
            | 'I'
            | 'i'
            | 'J'
            | 'j'
        ;
protected NumberSuffix
        :
            IntSuffix
            | 'F'
            | 'f'
        ;
protected
Digit
        :       '0'..'9'


        ;


protected
Exponent
        :       ( 'e' | 'E' ) ( '+' | '-' )? ( Digit )+
        ;


Number
        :       ( ( Digit )+ ( '.' | 'e' | 'E' ) )=> ( Digit )+
                ( '.' ( Digit )* ( Exponent )?
                | Exponent
                ) 
                ( NumberSuffix
                )*
				
        |       ( "..." )=> "..."       { _ttype = VARARGS;     }

        |       '.'                     { _ttype = DOT; }
                ( ( Digit )+ ( Exponent )?
                                        { _ttype = Number;   }
                    ( NumberSuffix
                    )*
                )?

        |       '0' ( '0'..'7' )*       
                ( NumberSuffix
                )*

        |       '1'..'9' ( Digit )*     
                ( NumberSuffix
                )*

        |       '0' ( 'x' | 'X' ) ( 'a'..'f' | 'A'..'F' | Digit )+
                ( IntSuffix
                )*
        ;

IDMEAT
        :
                i:ID                {
                                        
                                        if ( i.getType() == LITERAL___extension__ ) {
                                                $setType(Token.SKIP);
                                        }
                                        else {
                                                $setType(i.getType());
                                        }
                                        
                                    }
        ;
        
protected ID
        options 
                {
                testLiterals = true; 
                }
        :       ( 'a'..'z' | 'A'..'Z' | '_' | '$')
                ( 'a'..'z' | 'A'..'Z' | '_' | '$' | '0'..'9' )*
        ;
        
        WideCharLiteral
        :
                'L' CharLiteral
                                { $setType(CharLiteral); }
        ;
SCHEMA_IDMEAT
        :
                i:SCHEMA_ID                {
                                        
                                        if ( i.getType() == LITERAL___extension__ ) {
                                                $setType(Token.SKIP);
                                        }
                                        else {
                                                $setType(i.getType());
                                        }
                                        
                                    }
        ;

protected SCHEMA_ID
        options 
                {
                testLiterals = true; 
                }
        :       ( '#' )
                ( 'a'..'z' | 'A'..'Z' | '_' | '$')
                ( 'a'..'z' | 'A'..'Z' | '_' | '$' | '0'..'9' )*
        ;
        
META_STATEMENT_PREFIX
	:
		":stmnt:"
		;
		
META_EXPRESSION_PREFIX
	:
		":expr:"
		;

WideStringLiteral
        :
                'L' StringLiteral
                                { $setType(StringLiteral); }
        ;

StringLiteral
        :
                '"'
                ( ('\\' ~('\n'))=> Escape
                | ( '\r'        { newline(); }
                  | '\n'        {
                                newline();
                                }
                  | '\\' '\n'   {
                                newline();
                                }
                  )
                | ~( '"' | '\r' | '\n' | '\\' )
                )*
                '"'
        ;

