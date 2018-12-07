package de.uka.ilkd.key.util;

public class HorizontalLine extends MarkdownElement {
  public String toMarkdown() { return "\n ------- \n";}
  public String toHtml() { return "</hr>"; }
}
