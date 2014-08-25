// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;

import java.util.HashMap;

import org.antlr.runtime.LegacyCommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;

import antlr.ANTLRException;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.init.Includes;
import de.uka.ilkd.key.proof.io.IProofFileParser;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;

public class KeYParserF {

    private KeYParser keYParser;

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF,
	    ParserConfig schemaConfig, ParserConfig normalConfig,
	    HashMap taclet2Builder, ImmutableSet<Taclet> taclets) {
	LegacyCommonTokenStream stream = new LegacyCommonTokenStream(
		keYLexerF.getKeYLexer());
	this.keYParser = new KeYParser(mode, stream, schemaConfig,
		normalConfig, taclet2Builder, taclets);
    }

    public KeYParserF(ParserMode mode, TokenStream lexer,
	    ParserConfig schemaConfig, ParserConfig normalConfig,
	    HashMap taclet2Builder, ImmutableSet<Taclet> taclets) {
	this.keYParser = new KeYParser(mode, lexer, schemaConfig,
		normalConfig, taclet2Builder, taclets);
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF) {
	LegacyCommonTokenStream stream = new LegacyCommonTokenStream(
		keYLexerF.getKeYLexer());
	this.keYParser = new KeYParser(mode, stream);
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF,
	    JavaReader jr, Services services, NamespaceSet nss, AbbrevMap scm) {
	LegacyCommonTokenStream stream = new LegacyCommonTokenStream(
		keYLexerF.getKeYLexer());
	this.keYParser = new KeYParser(mode, stream, jr, services,
		nss, scm);
    }

    public KeYParserF(ParserMode mode, KeYLexerF keYLexerF, Services services,
	    NamespaceSet nss) {
	LegacyCommonTokenStream stream = new LegacyCommonTokenStream(
		keYLexerF.getKeYLexer());
	this.keYParser = new KeYParser(mode, stream, services, nss);
    }

    public void parseWith() throws ANTLRException {
	try {
	    this.keYParser.parseWith();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public ImmutableSet<Choice> getActivatedChoices() {
	return this.keYParser.getActivatedChoices();
    }

    public Term parseProblem() throws ANTLRException {
	try {
	    return this.keYParser.parseProblem();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public ImmutableSet<Taclet> getTaclets() {
	return this.keYParser.getTaclets();
    }

    public String getProfileName() {
	return this.keYParser.getProfileName();
    }

    public String getProofObligation() {
	return this.keYParser.getProofObligation();
    }

    public String getChooseContract() {
	return this.keYParser.getChooseContract();
    }

    public void proof(IProofFileParser prl) throws ANTLRException {
	try {
	    this.keYParser.proof(prl);
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public Term term() throws antlr.RecognitionException {
	try {
	    return this.keYParser.term();
	} catch (RecognitionException e) {
	    throw new antlr.RecognitionException(e.getMessage());
	}
    }

    public Term problem() throws ANTLRException {
	try {
	    return this.keYParser.problem();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public void profile() throws ANTLRException {
	try {
	    this.keYParser.profile();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public Term formula() throws ANTLRException {
	try {
	    return this.keYParser.formula();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public IdDeclaration id_declaration() throws antlr.RecognitionException {
	try {
	    return this.keYParser.id_declaration();
	} catch (RecognitionException e) {
	    throw new antlr.RecognitionException(e.getMessage());
	}
    }

    public String preferences() throws ANTLRException {
	try {
	    return this.keYParser.preferences();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public void parseIncludes() throws ANTLRException {
	try {
	    this.keYParser.parseIncludes();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public Includes getIncludes() {
	return this.keYParser.getIncludes();
    }

    public String bootClassPath() throws ANTLRException {
	try {
	    return this.keYParser.bootClassPath();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public ImmutableList<String> classPaths() throws ANTLRException {
	try {
	    return this.keYParser.classPaths();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public String javaSource() throws ANTLRException {
	try {
	    return this.keYParser.javaSource();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public void parseSorts() throws ANTLRException {
	try {
	    this.keYParser.parseSorts();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public void parseFuncAndPred() throws ANTLRException {
	try {
	    this.keYParser.parseFuncAndPred();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public HashMap<String, String> getCategory2Default() {
	return this.keYParser.getCategory2Default();
    }

    public void parseTacletsAndProblem() throws ANTLRException {
	try {
	    this.keYParser.parseTacletsAndProblem();
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }

    public ImmutableSet<Contract> getContracts() {
	return this.keYParser.getContracts();
    }

    public ImmutableSet<ClassInvariant> getInvariants() {
	return this.keYParser.getInvariants();
    }

    public NamespaceSet namespaces() {
	return this.keYParser.namespaces();
    }

    public void decls() throws antlr.RecognitionException {
	try {
	    this.keYParser.decls();
	} catch (RecognitionException e) {
	    throw new antlr.RecognitionException(e.getMessage());
	}
    }

    public Taclet taclet(DefaultImmutableSet<Choice> choices_)
	    throws ANTLRException {
	try {
	    return this.keYParser.taclet(choices_);
	} catch (RecognitionException e) {
	    throw new ANTLRException(e.getMessage());
	}
    }
}