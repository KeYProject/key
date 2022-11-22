package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.speclang.MergeContract;
import de.uka.ilkd.key.util.KeYResourceManager;

import java.io.File;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.net.URL;

public class TestPredicateConstruction {

	private final TermFactory tf;
	private final TermBuilder tb;
	private final NamespaceSet nss;
	private final Services services;
	private final KeyIO io;

	TestPredicateConstruction() {
		URL urlToTestFile = KeYResourceManager.getManager().getResourceFile(this, "test.key");
		services = HelperClassParsingTests.createServices(new File(urlToTestFile.getFile()));
		tb = services.getTermBuilder();
		nss = services.getNamespaces();
		tf = tb.tf();
		io = new KeyIO(services, nss);
	}

	public Term parseProblem(String s) {
		try {
			new Recoder2KeY(services, nss).parseSpecialClasses();
			return io.load(s).loadProblem().getProblemTerm();
		} catch (Exception e) {
			StringWriter sw = new StringWriter();
			PrintWriter pw = new PrintWriter(sw);
			e.printStackTrace(pw);
			throw new RuntimeException("Exc while Parsing:\n" + sw);
		}
	}

	public Term parse(String s) {
		try {
			return io.parseExpression(s);
		} catch (Exception e) {
			StringWriter sw = new StringWriter();
			PrintWriter pw = new PrintWriter(sw);
			e.printStackTrace(pw);
			throw new RuntimeException("Exc while Parsing:\n" + sw);
		}
	}

	public LoopInvariantGenerationResult shiftArrayToLeft() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "		while (i<a.length-1) {a[i] = a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult shiftArrayToLeftWithBreak() {
		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {"
					+ "if (i==a.length-1) break;"
					+ "else {a[i] = a[i+1];"
					+ "			i++;}}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult withFunc() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = Object.arrayFct(a[i]);" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult withoutFunc() {
		Term succFormula;

		try {
			succFormula =
					parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = a[i]+1;" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult stencil() {

		Term succFormula;

		try {
			succFormula = parse("{i:=1}\\<{" + "			while (i<a.length-1) {a[i] = a[i-1] + a[i+1];" + "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}
//
//	public void shiftArrayToLeftWithAiliasing() {
//		Term succFormula;
//		try {
//			succFormula = parse("{i:=0}\\<{" + "			while (i<a.length-1) {a[i] = b[i+1];" + "			i++;}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return null;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();
//
//		String[] arrLeft = { "noW(arrayRange(a,0,a.length))","noR(arrayRange(a,0,a.length))", "a.length > 10" };
//		String[] arrRight = { "a=null", "b=null", "a!=b", "a.length!=b.length" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return null;
//		}
//		
//		try {
//			for (String fml : arrRight) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return null;
//		}
//		
//		LIGNew curNew = new LIGNew(services, seq);
//		curNew.mainAlg();
//	}
//	
//	public void shiftArrayToLeftWithoutAiliasing() { //Done
//		Term succFormula;
//
//		try {
//			succFormula = parse("{i:=0}\\<{" + "			while (i<a.length-1) {a[i] = b[i+1];" + "			i++;}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return null;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();
//
//		String[] arrLeft = {"a!=null", "a.length > 10", "a!=b", "b!=null", "a.length=b.length"};
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return null;
//		}
//		LIGMultipleArrays loopInvGenerator = new LIGMultipleArrays(services, seq);
//		loopInvGenerator.mainAlg();
//	}
//
//	
	public LoopInvariantGenerationResult condition() {
		Term formula;
		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		//// a bit of a lengthy parsing
		try {
			
			formula = parse("{i:=0}\\<{while (i<=a.length-1) {"
							+ "				if(i > (a.length-1)/2){"
							+ "					a[i] = 1;"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = 0;"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
							+ "        //@ merge_proc \"MergeByIfThenElse\";\n"
							+ "			i++;}"
							+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		MergePointInline inlineMergePoints = new MergePointInline(formula.sub(1).javaBlock().program(), false, services);
		ProgramElement s = inlineMergePoints.inline();
		
		for (MergeContract mc : inlineMergePoints.getContracts()) {
			services.getSpecificationRepository().addMergeContract(mc);
		}
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
//		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = {"noR(arrayRange(a,0,a.length))", "noW(arrayRange(a,0,a.length))", "a.length>10" };
		String[] arrRight = {"a=null"};
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult conditionDifferentNumberOfEvents() {

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		try {
			
			formula = parse("{i:=0}\\<{while (i<a.length-1) {"
							+ "				if(i> (a.length-1)/2){"
							+ "					a[i] = a[i+1];"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = 1;"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
							+ "        //@ merge_proc \"MergeByIfThenElseAntecedent\";\n"
							+ "			i++;}"
							+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		MergePointInline inlineMergePoints = new MergePointInline(formula.sub(1).javaBlock().program(), false, services);
		ProgramElement s = inlineMergePoints.inline();
		
		for (MergeContract mc : inlineMergePoints.getContracts()) {
			services.getSpecificationRepository().addMergeContract(mc);
		}
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
		
//		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = { "noW(arrayRange(a,0,a.length))","noR(arrayRange(a,0,a.length))", "a.length>10" };
		String[] arrRight = {"a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult conditionWithDifferentEvents() {

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		try {
			
			formula = parse("{i:=1}\\<{while (i<a.length-1) {"
							+ "				if(i> (a.length-1)/2){"
							+ "					a[i] = a[i+1];"
							+ "				}\n"
							+ "				else {"
							+ " 				a[i] = a[i-1];"
							+ "				}"
							+ "				; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
							+ "        //@ merge_proc \"MergeByIfThenElseAntecedent\";\n"
							+ "			i++;}"
							+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		
		MergePointInline inlineMergePoints = new MergePointInline(formula.sub(1).javaBlock().program(), false, services);
		ProgramElement s = inlineMergePoints.inline();
		
		for (MergeContract mc : inlineMergePoints.getContracts()) {
			services.getSpecificationRepository().addMergeContract(mc);
		}
		
		if (!(s instanceof StatementBlock)) {
			s = new StatementBlock((Statement)s);
		}
		
		// recreate formula
		formula = tb.apply(formula.sub(0), tb.dia(JavaBlock.createJavaBlock((StatementBlock)s), tb.tt()));
		
//		System.out.println("Formula with merge point: "+ProofSaver.printAnything(formula, services));

		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length>10" };
		String[] arrRight = {"a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();

			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		return loopInvGenerator.generate();
	}

//
//	public void testCaseFor_mbps() {
//
//		Term formula;
//
//		try {
//			formula = parse("{i:=0}\\<{" + "			while (i<=a.length-1) {a[i] = 1;"
//										 + "            	sum= sum + a[i];"
//										 + "				i++;}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//
//		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		LIGMultipleArrays loopInvGenerator = new LIGMultipleArrays(services, seq);
//		loopInvGenerator.mainAlg();
//	}
//
//	
//	
//	public void testCase12() {
//
//		Term formula;
//
//		try {
//			formula = parse("{i:=0 || j:=0}\\<{"
//											+ "			while (i<=a.length-1 && j<=a.length-1) {a[i] = b[j];"
//											+ "				i++;"
//											+ "				j++;"
//											+ "}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//
//		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "a.length=b.length" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		LIGMultipleArrays loopInvGenerator = new LIGMultipleArrays(services, seq);
//		loopInvGenerator.mainAlg();
//	}
//
//	
//	public void testCase13() {
//
//		Term formula;
//
//		try {
//			formula = parse("{i:=0 || j:=b.length}\\<{"
//											+ "			while (i<=a.length-1 && j>=0) {a[i] = b[j];"
//											+ "				i++;"
//											+ "				j--;"
//											+ "}"
//					+ "		}\\>true");
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
//		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(formula), false, true).sequent();
//
//		String[] arrLeft = { /* "i=0", */"a!=null", "b!=null", "a.length=b.length" };
//		try {
//			for (String fml : arrLeft) {
//				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
//
//			}
//		} catch (Exception e) {
//			System.out.println(e.getMessage());
//			if (e.getCause() != null) {
//				System.out.println(e.getCause().getMessage());
//			}
//			e.printStackTrace();
//			return;
//		}
////		LIGMultipleArrays loopInvGenerator = new LIGMultipleArrays(services, seq);
////		loopInvGenerator.mainAlg();
//	}


//======================================================================================================================
//													Nested Loops
//======================================================================================================================
public LoopInvariantGenerationResult basicEx0() {

	Term succFormula;

	try {
		succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<a.length-1) {"
													+ "			while (j<a.length-1) {"
													+ "				a[j] = 1;"
													+ "				j++;}"
													+ "			i++;}"
													+ "		}\\>true");
	} catch (Exception e) {
		System.out.println(e.getMessage());
		if (e.getCause() != null) {
			System.out.println(e.getCause().getMessage());
		}
		e.printStackTrace();
		return null;
	}
	Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

	String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
	String[] arrRight = { "a=null" };
	try {
		for (String fml : arrLeft) {
			seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
		}
	} catch (Exception e) {
		System.out.println(e.getMessage());
		if (e.getCause() != null) {
			System.out.println(e.getCause().getMessage());
		}
		e.printStackTrace();
		return null;
	}

	try {
		for (String fml : arrRight) {
			seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
		}
	} catch (Exception e) {
		System.out.println(e.getMessage());
		if (e.getCause() != null) {
			System.out.println(e.getCause().getMessage());
		}
		e.printStackTrace();
		return null;
	}

	final LIGNested loopInvGenerator = new LIGNested(seq, services);
	return loopInvGenerator.generate();
}

	public LoopInvariantGenerationResult basicEx1() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<a.length-1) {"
					+ "												while (j<=a.length-1) {"
					+ "													a[j] = 1;"
					+ "													j++;}"
					+ "												i++;}"
					+ "									}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrRight = { "a=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNested loopInvGenerator = new LIGNested(seq, services);
		return loopInvGenerator.generate();
	}

//======================================================================================================================
//											Nested Loops with Multiple Arrays
//======================================================================================================================

	public LoopInvariantGenerationResult basicMltpArrSameIndex() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{" + "		while (i<a.length-1) {"
					+ "			while (j<b.length-1) {"
					+ "				a[i] = b[i];"
					+ "				}"
					+ "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10","noW(arrayRange(b,0,b.length-1))","noR(arrayRange(b,0,b.length-1))", "b.length > 10" };
		String[] arrRight = { "a=null", "b=null" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNestedMltpArr loopInvGenerator = new LIGNestedMltpArr(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult basicMltpArrDiffIndex() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<a.length-1) {"
					+ "			while (j<b.length-1) {"
					+ "				a[i] = b[j];"
					+ "				j++;}"
					+ "			i++;}"
					+ "		}\\>true");
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}
		Sequent seq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(succFormula), false, true).sequent();

		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10","noW(arrayRange(b,0,b.length-1))","noR(arrayRange(b,0,b.length-1))", "b.length > 10" };
		String[] arrRight = { "a=null", "b=null", "a=b" };
		try {
			for (String fml : arrLeft) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), true, true).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		try {
			for (String fml : arrRight) {
				seq = seq.addFormula(new SequentFormula(parse(fml)), false, false).sequent();
			}
		} catch (Exception e) {
			System.out.println(e.getMessage());
			if (e.getCause() != null) {
				System.out.println(e.getCause().getMessage());
			}
			e.printStackTrace();
			return null;
		}

		final LIGNestedMltpArr loopInvGenerator = new LIGNestedMltpArr(seq, services);
		return loopInvGenerator.generate();
	}






	public static void main(String[] args) {
		TestPredicateConstruction tpc = new TestPredicateConstruction();
		LoopInvariantGenerationResult result;
		long start = System.currentTimeMillis();
//		result = tpc.shiftArrayToLeft();//Precise Result
//		result = tpc.shiftArrayToLeftWithBreak();//Precise Result
//		result = tpc.condition();//Precise Result
//		result = tpc.conditionDifferentNumberOfEvents();//Precise Result
//		result = tpc.conditionWithDifferentEvents(); //Change the s0 in LIGNew. Precise Result except that it doesn't have the noWaR(a[1]). Because we don't allow breaking the array more than once.
//		result = tpc.withFunc();
//		result = tpc.withoutFunc();
//		result = tpc.stencil(); //Change the s0 in LIGNew. Precise Result except that it doesn't have the noWaR(a[1]). Because we don't allow breaking the array more than once.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
		result = tpc.basicMltpArrDiffIndex();
//		System.out.println(result);
		long end = System.currentTimeMillis();
		System.out.println("Loop Invariant Generation took " + (end - start) + " ms");
	}
}