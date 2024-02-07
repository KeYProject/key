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
		URL urlToTestFile = KeYResourceManager.getManager().getResourceFile(this, "test.key");//here we can define array a and b as 1D, 2D, etc.
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
			succFormula = parse("{i:=0}\\<{" + "		while (i<=a.length-2) {a[i] = a[i+1];" + "			i++;}"
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
//		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10" };
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
//		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult interAndIntra() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0}\\<{"
					+ "		while (i<=a.length-2) {"
					+"			a[i] = a[i+1];"
					+"			sum = sum + a[i];"
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

//		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10" };
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

//		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
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

//		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10" };
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

//		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
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
//		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10" };
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
//		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
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
//		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10" };
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
//		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
		return loopInvGenerator.generate();
	}


	public LoopInvariantGenerationResult interDep() {
		Term succFormula;

		try {
			succFormula =
					parse("{i:=0}\\<{"
							+ "			while (i<=a.length-1) {"
							+"		        a[i] = a[i]+1;"
							+"				sum = sum + a[i];"
							+ "			    i++;}"
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
//		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10", "sum = 0" };
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
//		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
		return loopInvGenerator.generate();
	}


	public LoopInvariantGenerationResult stencil() {

		final Term succFormula;

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

//		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10" };
		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length > 10" };
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

//		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
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
//		String[] arrLeft = {"noR(arrayRange(a,0,a.length))", "noW(arrayRange(a,0,a.length))", "a.length>10" };
		String[] arrLeft = {"relaxedNoR(arrayRange(a,0,a.length))", "relaxedNoW(arrayRange(a,0,a.length))", "a.length>10" };
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
//		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult conditionDifferentNumberOfEvents() {

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		try {
			
			formula = parse("{i:=0}\\<{while (i<=a.length-2) {"
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
//		String[] arrLeft = { "noW(arrayRange(a,0,a.length))","noR(arrayRange(a,0,a.length))", "a.length>10" };
		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length))","relaxedNoR(arrayRange(a,0,a.length))", "a.length>10" };
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

//		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult conditionWithDifferentEvents() {

		Term formula;

		Recoder2KeY r2k = new Recoder2KeY(services, nss);
		
		try {
			
			formula = parse("{i:=1}\\<{while (i <= a.length-2) {"
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
//		String[] arrLeft = { "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length>10" };
		String[] arrLeft = { "relaxedNoW(arrayRange(a,0,a.length-1))","relaxedNoR(arrayRange(a,0,a.length-1))", "a.length>10" };
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

//		final LIGNew loopInvGenerator = new LIGNew(seq, services);
		final LIGNewRelaxed loopInvGenerator = new LIGNewRelaxed(seq, services);
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
//										Single Loops w/ inner dependencies
//======================================================================================================================





//======================================================================================================================
//													Nested Loops
//======================================================================================================================

public LoopInvariantGenerationResult basicEx0() {//Change length of arrays in AbstractLoopInvariantGenerator to 1

	Term succFormula;

	try {
		succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<=a.length-1) {"
													+ "			while (j<=a.length-1) {"
													+ "				a[j] = a[j]+1;"
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


//======================================================================================================================
//											Nested Loops with Multiple Arrays
//======================================================================================================================

	public LoopInvariantGenerationResult basicMltpArrDiffIndex() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<=a.length-1) {"
					+ "			while (j<=b.length-1) {"
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

		String[] arrLeft = {"a.length=b.length", "noW(arrayRange(a,0,a.length-1))","noR(arrayRange(a,0,a.length-1))", "a.length > 10","noW(arrayRange(b,0,b.length-1))","noR(arrayRange(b,0,b.length-1))", "b.length > 10" };
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

//======================================================================================================================
//											Nested Loops with Multi Dimensial Arrays
//======================================================================================================================

	public LoopInvariantGenerationResult basicMDArray0() {

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

		String[] arrLeft = { "noW(infiniteUnion{int k;}(\\if(k>=0 & k<a.length)\\then(singleton(a,arr(k)))\\else(empty)))",
							 "noR(infiniteUnion{int k;}(\\if(k>=0 & k<a.length)\\then(singleton(a,arr(k)))\\else(empty)))",
							 "a.length > 10",
							 "noW(infiniteUnion{int k;}(\\if (k>=0 & k<b.length)\\then(singleton(b,arr(k)))\\else(empty)))",
							 "noR(infiniteUnion{int k;}(\\if (k>=0 & k<b.length)\\then(singleton(b,arr(k)))\\else(empty)))",
				             "b.length > 10" };
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

	public LoopInvariantGenerationResult basicMDArray() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<a.length-1) {"
					+ "			while (j<b.length-1) {"
					+ "				a[i][j] = b[i][j];"
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

		String[] arrLeft = {
				"noW(infiniteUnion{int k;}(\\if(k>=0 & k<=a.length-1)\\then(arrayRange(a[k],0,a.length-1))\\else (empty)))",
				"noR(infiniteUnion{int k;}(\\if(k>=0 & k<=a.length-1)\\then(arrayRange(a[k],0,a.length-1))\\else(empty)))",
				"a.length > 10",
				"noW(infiniteUnion{int k;}(\\if (k>=0 & k<=b.length-1)\\then(arrayRange(b[k],0,b.length-1))\\else(empty)))",
				"noR(infiniteUnion{int k;}(\\if (k>=0 & k<=b.length-1)\\then(arrayRange(b[k],0,b.length-1))\\else(empty)))",
				"b.length > 10",
				"a.length = b.length"	};
		String[] arrRight = { "a=null", "b=null", "a=b", "\\forall int r;(\\forall int s;(a[r]=b[s]))" };
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

		final LIGNestedMDmnslArr loopInvGenerator = new LIGNestedMDmnslArr(seq, services);
		return loopInvGenerator.generate();
	}

	public LoopInvariantGenerationResult basicMDArray42() {

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<a.length-1) {"
					+ "			while (j<b.length-1) {"
					+ "				a[i][i] = 0;"
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

		String[] arrLeft = {
				"noW(infiniteUnion{int k;}(\\if(k>=0 & k<=a.length-1)\\then(arrayRange(a[k],0,a.length))\\else (empty)))",
				"noR(infiniteUnion{int k;}(\\if(k>=0 & k<=a.length-1)\\then(arrayRange(a[k],0,a.length))\\else(empty)))",
				"a.length > 10",
				"noW(infiniteUnion{int k;}(\\if (k>=0 & k<=b.length-1)\\then(arrayRange(b[k],0,b.length))\\else(empty)))",
				"noR(infiniteUnion{int k;}(\\if (k>=0 & k<=b.length-1)\\then(arrayRange(b[k],0,b.length))\\else(empty)))",
				"b.length > 10",
				"a.length = b.length"	};
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

		final LIGNestedMDmnslArr loopInvGenerator = new LIGNestedMDmnslArr(seq, services);
		return loopInvGenerator.generate();
	}

//======================================================================================================================
//											Proving Loop Invariant
//======================================================================================================================

//======================================================================================================================
//======================================================================================================================
//======================================================================================================================
//												Polybench
//======================================================================================================================
//======================================================================================================================
//======================================================================================================================

//==================================================Correlation=========================================================
public LoopInvariantGenerationResult correlation_init_array() {//Change length of arrays in AbstractLoopInvariantGenerator to 1

	final Term succFormula;

	try {
		succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<=N-1) {"
				+ "			while (j<=M-1) {"
				+ "				a[i][j] = 1;"
				+ "				j++;}"
				+ "			j = 0; i++;}"
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

//	String[] arrLeft = { "wellFormed(heap)", "a.<created>=TRUE", "wellFormedMatrix(a, heap)", "noW(arrayRange(a,0,a.length-1))",
//			"noW(matrixRange(heap,a,0,N-1,0,M-1))","noR(matrixRange(heap,a,0,N-1,0,M-1))",
//			"a.length > N", "a[0].length > M", "N >10","M >10"};
	String[] arrLeft = { "wellFormed(heap)", "a.<created>=TRUE", "wellFormedMatrix(a, heap)", "relaxedNoW(arrayRange(a,0,a.length-1))",
			"relaxedNoW(matrixRange(heap,a,0,N-1,0,M-1))","relaxedNoR(matrixRange(heap,a,0,N-1,0,M-1))",
			"a.length > N", "a[0].length > M", "N >10","M >10"};
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

//	final LIGNestedMDarr loopInvGenerator = new LIGNestedMDarr(seq, services);
	final NestedLIGNewRelaxed loopInvGenerator = new NestedLIGNewRelaxed(seq, succFormula, services);
	return loopInvGenerator.generate();
}
//======================================================================================================================================

	public LoopInvariantGenerationResult correlation_print_array() {//Change length of arrays in AbstractLoopInvariantGenerator to 1

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<=N-1) {"
														+ "			while (j<=M-1) {"
														+ "			if(((i * M) + j) / 20 == 0){"
														+ "					x = a[i][j];"
														+ "				}"
														+ "			else {"
														+ " 				x = 1;"
														+ "				}"
														+ "			; // this is just a comment, the semicolon is replaced by a merge_point(i);\n"
														+ "        //@ merge_proc \"MergeByIfThenElseAntecedent\";\n"
														+ "				j++;"
														+ "				}"
														+ "				j = 0;"
														+ "				i++;}"
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

//		String[] arrLeft = { "wellFormed(heap)", "a.<created>=TRUE", "wellFormedMatrix(a, heap)", "noW(arrayRange(a,0,a.length-1))",
//				"noW(matrixRange(heap,a,0,N-1,0,M-1))","noR(matrixRange(heap,a,0,N-1,0,M-1))",
//				"a.length > N", "a[0].length > M", "N >10","M >10", "N = M"};
		String[] arrLeft = { "wellFormed(heap)", "a.<created>=TRUE", "wellFormedMatrix(a, heap)", "relaxedNoW(arrayRange(a,0,a.length-1))",
				"relaxedNoW(matrixRange(heap,a,0,N-1,0,M-1))","relaxedNoR(matrixRange(heap,a,0,N-1,0,M-1))",
				"a.length > N", "a[0].length > M", "N >10","M >10"};
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

//		final LIGNestedMDarr loopInvGenerator = new LIGNestedMDarr(seq, services);
		final NestedLIGNewRelaxed loopInvGenerator = new NestedLIGNewRelaxed(seq, succFormula, services);
		return loopInvGenerator.generate();
	}

//======================================================================================================================================

	public LoopInvariantGenerationResult gem_ver_scope_1() {//Change length of arrays in AbstractLoopInvariantGenerator to 1

		Term succFormula;

		try {
			succFormula = parse("{i:=0 || j:=0}\\<{" + "		while (i<=N-1) {"
														+ "			while (j<=M-1) {"
														+ "				a[i][j]=a[i][j]+1;"
														+ "				j++;"
														+ "			}"
														+ "			j = 0;"
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

//		String[] arrLeft = { "wellFormed(heap)", "a.<created>=TRUE", "wellFormedMatrix(a, heap)", "noW(arrayRange(a,0,a.length-1))",
//				"noW(matrixRange(heap,a,0,N-1,0,M-1))","noR(matrixRange(heap,a,0,N-1,0,M-1))",
//				"a.length > N", "a[0].length > M", "N >10","M >10", "N = M"};
		String[] arrLeft = { "wellFormed(heap)", "a.<created>=TRUE", "wellFormedMatrix(a, heap)", "relaxedNoW(arrayRange(a,0,a.length-1))",
				"relaxedNoW(matrixRange(heap,a,0,N-1,0,M-1))","relaxedNoR(matrixRange(heap,a,0,N-1,0,M-1))",
				"a.length > N", "a[0].length > M", "N >10","M >10"};
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

//		final LIGNestedMDarr loopInvGenerator = new LIGNestedMDarr(seq, services);
		final NestedLIGNewRelaxed loopInvGenerator = new NestedLIGNewRelaxed(seq, succFormula, services);
		return loopInvGenerator.generate();
	}


	//======================================================================================================================================
	public static void main(String[] args) {
		TestPredicateConstruction tpc = new TestPredicateConstruction();
		LoopInvariantGenerationResult result;
		long start = System.currentTimeMillis();
		result = tpc.shiftArrayToLeft();//Precise Result. Relaxed works.
//		result = tpc.interAndIntra();//New. Relaxed works. But noR(a[0]) is missing.
//		result = tpc.shiftArrayToLeftWithBreak();//Precise Result. Relaxed works.
//		result = tpc.condition();//Precise Result. Relaxed works.
//		result = tpc.conditionDifferentNumberOfEvents();//Precise Result. Relaxed works.
//		result = tpc.conditionWithDifferentEvents(); //Change the s0 in LIGNew. Precise Result except that it doesn't have the noWaR(a[1]). Because we don't allow breaking the array more than once. Relaxed works.
//		result = tpc.withFunc(); //Normal works. Relaxed works.
//		result = tpc.withoutFunc(); //Normal works. Relaxed works.
//		result = tpc.interDep(); //New. Normal works. Relaxed works.
//		result = tpc.stencil(); //Change the s0 in LIGNew. Precise Result except that it doesn't have the noWaR(a[1]). Because we don't allow breaking the array more than once. Relaxed works.
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//		result = tpc.basicEx0();//Precise Result
//		result = tpc.basicMltpArrDiffIndex();
//		System.out.println(result);
///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//		result = tpc.correlation_init_array();// 00:31
//		result = tpc.correlation_print_array();// 26min
//		result = tpc.gem_ver_scope_1();// 1:07
		long end = System.currentTimeMillis();
		System.out.println("Loop Invariant Generation took " + (end - start) + " ms");
	}
}