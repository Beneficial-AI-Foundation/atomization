package isabelle

import scala.io.Source
import java.io.PrintWriter
import scala.sys.process._
import scala.collection.mutable

object Atomizer_graph {

  def replaceLatexSymbols(body: String): String =
    body
      .replace("\\<Rightarrow>", "⇒")
      .replace("\\<times>", "x")

  // New case class for an atom
  case class Atom(identifier: String, body: String, statementType: String, deps: Seq[String])

  // New helper: extract the proof text from the spans after index i until an allowed span is reached.
  private def extractProofText(spans: List[Command_Span.Span], i: Int): String = {
    val allowed = Set("fun", "definition", "theorem", "lemma", "corollary", "proposition")
    val proofBuilder = new StringBuilder
    var j = i + 1
    while(j < spans.length && !allowed.contains(spans(j).name)) {
      if(spans(j).name.contains("proof"))
        proofBuilder.append(spans(j).content.map(_.source).mkString(" ") + " ")
      j += 1
    }
    proofBuilder.toString
  }

  // Refactored processSpan that takes an index and uses extractProofText.
  private def processSpanAtIndex(i: Int,
      spans: List[Command_Span.Span],
      indices: mutable.Map[String, Int],
      nodes: mutable.Buffer[String]
  ): Option[Atom] = {
    val allowed = List("fun", "definition", "theorem", "lemma", "corollary", "proposition")
    val span = spans(i)
    if (!allowed.contains(span.name)) None
    else {
      val rawBody = span.content.map(_.source).mkString(" ")
      val proofText = extractProofText(spans, i)
      val combinedText = rawBody + " " + proofText
      val replaced = replaceLatexSymbols(rawBody)
      // Clean the body for display: remove backslashes, quotes, and newlines.
      val cleanBody = replaced.replaceAll("[\\\\\"]", "").replaceAll("[\\r\\n]", " ")
      val statementType = span.name
      val identifier = span.content
        .find(_.is_ident)
        .map(_.source.mkString(""))
        .getOrElse("unnamed_" + statementType + indices(statementType))
      if (identifier.contains("unnamed"))
        indices(statementType) += 1
      nodes += identifier
      // Dependencies: nodes seen so far, found in the combined text.
      // Simple contains check might be more appropriate for Isabelle
      val deps = nodes.filter(n => n != identifier && combinedText.contains(n)).toSeq
      Some(Atom(identifier, cleanBody, statementType, deps))
    }
  }

  // Helper: converts an Atom to a JSON fragment
  private def atomToJson(atom: Atom): String =
    s""""${atom.identifier}_atom" : {
       |  "identifier": "${atom.identifier}",
       |  "body": "${atom.body}",
       |  "statement_type": "${atom.statementType}",
       |  "language": "Isabelle",
       |  "deps": "[${atom.deps.mkString(", ")}]"
       |}""".stripMargin

  // Refactored mk_json using processSpanAtIndex over span indices.
  def mk_json(spans: List[Command_Span.Span]): String = {
    val nodes = mutable.Buffer[String]()
    val indices = mutable.Map(
      "fun"         -> 1,
      "definition"  -> 1,
      "theorem"     -> 1,
      "lemma"       -> 1,
      "corollary"   -> 1,
      "proposition" -> 1
    )
    val atoms = for {
      i <- spans.indices
      atomOpt = processSpanAtIndex(i, spans, indices, nodes)
      if atomOpt.isDefined
    } yield atomOpt.get
    val jsonAtoms = atoms.map(atomToJson)
    "{\n\"Atoms\": [" + jsonAtoms.mkString(",\n") + "]\n}"
  }

  // Refactored mk_dot similarly using processSpanAtIndex.
  def mk_dot(spans: List[Command_Span.Span], dot_file: Path): Unit = {
    val nodes = mutable.Buffer[String]()
    val indices = mutable.Map(
      "fun"         -> 1,
      "definition"  -> 1,
      "theorem"     -> 1,
      "lemma"       -> 1,
      "corollary"   -> 1,
      "proposition" -> 1
    )
    val atoms = for {
      i <- spans.indices
      atomOpt = processSpanAtIndex(i, spans, indices, nodes)
      if atomOpt.isDefined
    } yield atomOpt.get

    val nodeLines = atoms.map { atom =>
      val shapeAttr = if (atom.statementType == "definition" || atom.statementType == "fun")
                        "shape=square" else ""
      val escapedBody = atom.body.replace("\"", "\\\"").replace("\\", "\\\\")
      val tooltipAttr = s"""tooltip="${escapedBody}""""
      val attrs = Seq(shapeAttr, tooltipAttr).filter(_.nonEmpty).mkString(", ")
      s"""    "${atom.identifier}" [${attrs}];"""
    }
    val edgeLines = atoms.flatMap { atom =>
      atom.deps.map(dep => s"""    "${atom.identifier}" -> "$dep";""")
    }
    val dotStr = "digraph G {\n" +
      (nodeLines ++ edgeLines).mkString("\n") +
      "\n}\n"
    File.write(dot_file, dotStr)
    println(s"DOT file written to: " + dot_file)
  }

  def mk_png(dot_file: Path, png_file: Path): Unit = {
    val cmd = s"dot -Tpng ${dot_file.implode} -o ${png_file.implode}"
    val exitCode = cmd.!
    if (exitCode == 0)
      println(s"PNG file generated: " + png_file)
    else
      println(s"Error generating PNG file. Exit code: " + exitCode)
  }

  def mk_svg(dot_file: Path, svg_file: Path): Unit = {
    val cmd = s"dot -Tsvg ${dot_file.implode} -o ${svg_file.implode}"
    val exitCode = cmd.!
    if (exitCode == 0)
      println(s"SVG file generated: " + svg_file)
    else
      println(s"Error generating SVG file. Exit code: " + exitCode)
  }

  def main(args: Array[String]): Unit = {
    if (args.length != 2) {
      println("Usage: isabelle scala -e 'atomizer_2.scala' <theory_file.thy> <output_dir>")
      sys.exit(1)
    }

    val thy_file = Path.explode(args(0))
    if (!thy_file.is_file) {
      println(s"Error: File not found - " + thy_file)
      sys.exit(1)
    }

    val output_dir = Path.explode(args(1))
    if (!output_dir.is_dir) {
      println(s"Error: Output directory not found - " + output_dir)
      sys.exit(1)
    }

    type Keywords = List[(String, Keyword.Spec)]
    val thy_keywords: Keywords = List(
      ("%", Keyword.Spec()),
      ("(", Keyword.Spec()),
      (")", Keyword.Spec()),
      (",", Keyword.Spec()),
      ("::", Keyword.Spec()),
      (":", Keyword.Spec()),
      ("..", Keyword.Spec()),
      ("=", Keyword.Spec()),
      ("and", Keyword.Spec()),
      ("[code]", Keyword.Spec()),
      ("export_code", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("export_code"))),
      ("text", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("section", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("subsection", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("subsubsection", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("fun", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("fun"))),
      ("function", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("function"))),
      ("datatype", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("datatype"))),
      ("definition", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("definition"))),
      ("theory", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("theory"))),
      ("proof", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("proof"))),
      ("apply", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("apply"))),
      ("fixes", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("fixes"))),
      ("lemma", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("lemma"))),
      ("theorem", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("theorem"))),
      ("corollary", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("corollary"))),
      ("proposition", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("proposition"))),
      ("qed", Keyword.Spec(kind = Keyword.QED, tags = List("qed"))),
      ("by", Keyword.Spec(kind = Keyword.PRF_ASM_GOAL, tags = List("by"))),
      ("end", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("end")))
    )

    val thy_syntax = Outer_Syntax.empty.add_keywords(thy_keywords)
    val theory_content = File.read(thy_file)
    val spans = thy_syntax.parse_spans(theory_content)
    
    val file_name = thy_file.implode.replaceAll("\\.thy$", "")
    val base_name = file_name.substring(file_name.lastIndexOf('/') + 1)
    val json_file = Path.explode(output_dir.implode + "/" + base_name + ".json")
    val json_content = mk_json(spans)
    
    File.write(json_file, json_content)
    println(s"JSON output written to: " + json_file)

    val dot_file = Path.explode(output_dir.implode + "/" + base_name + ".dot")
    mk_dot(spans, dot_file)

    val png_file = Path.explode(output_dir.implode + "/" + base_name + ".png")
    mk_png(dot_file, png_file)

    val svg_file = Path.explode(output_dir.implode + "/" + base_name + ".svg")
    mk_svg(dot_file, svg_file)
  }
}
