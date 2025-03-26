package isabelle

import scala.io.Source
import java.io.PrintWriter
import scala.sys.process._
import scala.collection.mutable
import java.nio.file.{Files, Paths, Path => JPath}
import scala.jdk.CollectionConverters._

object Atomizer_graph {

  // Method to read LaTeX symbols from a JSON file
  def readLatexSymbolsFromFile(filePath: String): Map[String, String] = {
    val jsonContent = File.read(Path.explode(filePath))
    val json = JSON.parse(jsonContent)
    json match {
      case JSON.Object(map) =>
        map.get("symbols") match {
          case Some(JSON.Object(symbols)) => 
            symbols.map { case (k, v) => 
              (k, v.asInstanceOf[String])
            }
          case _ => error("Invalid JSON format: missing 'symbols' object")
        }
      case _ => error("Invalid JSON format in latex symbols file")
    }
  }

  // Updated replaceLatexSymbols method
  def replaceLatexSymbols(body: String, latexSymbols: Map[String, String]): String = {
    var updatedBody = body
    for ((latex, symbol) <- latexSymbols) {
      updatedBody = updatedBody.replace(latex, symbol)
    }
    updatedBody
  }

  // New case class for an atom
  case class Atom(identifier: String, body: String, statementType: String, deps: Set[String])

  // New helper: extract the proof text from the spans after index i until an allowed span is reached.
  private def extractProofText(spans: List[Command_Span.Span], i: Int): String = {
    val allowed = Set("fun", "definition", "theorem", "lemma", "corollary", "proposition")
    val proofBuilder = new StringBuilder
    var j = i + 1
    while(j < spans.length && !allowed.contains(spans(j).name)) {
      if(spans(j).name.contains("proof") || spans(j).name.contains("by"))
        proofBuilder.append(spans(j).content.map(_.source).mkString(" ") + " ")
      j += 1
    }
    proofBuilder.toString
  }

  // Refactored processSpan that takes an index and uses extractProofText.
  private def processSpanAtIndex(i: Int,
      spans: List[Command_Span.Span],
      indices: mutable.Map[String, Int],
      nodes: mutable.Buffer[String],
      latexSymbols: Map[String, String]
  ): Option[Atom] = {
    val allowed = List("fun", "definition", "theorem", "lemma", "corollary", "proposition")
    val span = spans(i)
    if (!allowed.contains(span.name)) None
    else {
      val rawBody = span.content.map(_.source).mkString(" ")
      val proofText = extractProofText(spans, i)
      val combinedText = rawBody + " " + proofText
      val replaced = replaceLatexSymbols(rawBody, latexSymbols)
      // Clean the body for display: remove backslashes, quotes.
      //val cleanBody = replaced.replaceAll("[\\\\\"]", "").replaceAll("[\\r\\n]", " ")
      val cleanBody = replaced.replaceAll("[\\\\\"]", "")
      val statementType = span.name
      val identifier = span.content
        .find(_.is_ident)
        .map(_.source.mkString(""))
        .getOrElse("unnamed_" + statementType + indices(statementType))
      if (identifier.contains("unnamed"))
        indices(statementType) += 1
      nodes += identifier
      // Dependencies: nodes seen so far, found in the combined text.
      val deps = nodes.filter(n => n != identifier && combinedText.contains(n + " ")).toSet
      Some(Atom(identifier, cleanBody, statementType, deps))
    }
  }

  private def atomToJson(atom: Atom): JSON.Object.T = {
    JSON.Object(
      "identifier" -> atom.identifier,
      "body" -> atom.body,
      "statement_type" -> atom.statementType,
      "language" -> "Isabelle",
      "deps" -> atom.deps.toList
    )
  }

  // Refactored mk_json using processSpanAtIndex over span indices.
  def mk_json(spans: List[Command_Span.Span], latexSymbols: Map[String, String]): String = {
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
      atomOpt = processSpanAtIndex(i, spans, indices, nodes, latexSymbols)
      if atomOpt.isDefined
    } yield atomOpt.get
    val jsonAtoms = atoms.map(atomToJson).toList
    JSON.Format(JSON.Object("Atoms" -> jsonAtoms))
  }

  def main(args: Array[String]): Unit = {
    if (args.length != 3) {
      println("Usage: isabelle scala -e 'atomizer_2.scala' <theory_file.thy> <output_dir> <latex_symbols_file>")
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


    val latexSymbolsFile = args(2)
    val latexSymbols = readLatexSymbolsFromFile(latexSymbolsFile)

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
      ("[simp]", Keyword.Spec()),
      ("export_code", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("export_code"))),
      ("text", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("section", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("subsection", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("subsubsection", Keyword.Spec(kind = Keyword.DOCUMENT_BODY)),
      ("fun", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("fun"))),
      ("function", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("function"))),
      ("abbreviation", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("fun"))),
      ("datatype", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("datatype"))),
      ("definition", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("definition"))),
      ("theory", Keyword.Spec(kind = Keyword.THY_DEFN, tags = List("theory"))),
      ("proof", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("proof"))),
      ("by", Keyword.Spec(kind = Keyword.PRF_GOAL, tags = List("by"))),
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
    val base_path = thy_file.expand.implode
    val file_name = thy_file.implode.replaceAll("\\.thy$", "")
    val base_name = file_name.substring(file_name.lastIndexOf('/') + 1)
    val json_file = Path.explode(output_dir.implode + "/" + base_name + ".json")
    val json_content = mk_json(spans, latexSymbols)
    
    File.write(json_file, json_content)
    println(s"JSON output written to: " + json_file)
  }
}
