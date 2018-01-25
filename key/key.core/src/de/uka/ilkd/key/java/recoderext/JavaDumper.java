package de.uka.ilkd.key.java.recoderext;

import recoder.java.NonTerminalProgramElement;
import recoder.java.CompilationUnit;
import recoder.java.SourceElement;

public class JavaDumper {

	public static void dump(SourceElement elem) {
		dump(elem, 0);
	}

	private static void dump(SourceElement elem, int level) {
		String s;
		try {
			s = elem.toString();
		} catch(Throwable e) {
			s = elem.getClass() + "xxx";
		}
		System.out.println(indent(level) + first20(s));
		System.out.println(indent(level) + " " + elem.getStartPosition() + " - " + elem.getEndPosition());
		
		if (elem instanceof NonTerminalProgramElement) {
			NonTerminalProgramElement nt = (NonTerminalProgramElement) elem;
			for(int i = 0; i < nt.getChildCount(); i++) {
				dump(nt.getChildAt(i), level+1);
			}
		}
	}

	private static String first20(String string) {
		if(string.length() > 200)
			return string.substring(0, 20) + "...";
		else 
			return string;
	}

	private static String indent(int level) {
		StringBuilder sb = new StringBuilder();
				for (int i = 0; i < level; i++) {
					sb.append("  ");
				}
				return sb.toString();
	}

}
