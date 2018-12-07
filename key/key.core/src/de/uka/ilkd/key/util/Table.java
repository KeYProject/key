package de.uka.ilkd.key.util;

import java.util.List;

public class Table extends MarkdownElement {
  public List<List<String>> tableContent;
  public List<String> header;

  public Table(List<String> header, List<List<String>> tableContext) {
    this.header = header;
    this.tableContent = tableContent;
  }

  public String toHtml() {
    StringBuilder sb = new StringBuilder();
    sb.append("<table>");
    sb.append("<tr>");
    header.forEach(item -> sb.append("<th>").append(item).append("</th>"));
    sb.append("</tr>");
    tableContent.forEach(row -> {
      sb.append("<tr>");
      row.forEach(cell -> {
        sb.append("<td>").append(cell).append("</td>");
      });
      sb.append("</tr>");
    });
    return sb.toString();
  }


  public String toMarkdown() {
    StringBuilder sb = new StringBuilder();
    sb.append("|");
    header.forEach(item -> sb.append(item).append(" | "));
    sb.append("\n");
    header.forEach(item -> sb.append("-- | "));

    tableContent.forEach(row -> {
      sb.append(" ");
      row.forEach(cell -> {
        sb.append(cell).append(" | ");
      });
      sb.append("| \n");
    });
    return sb.toString();
  }

}
