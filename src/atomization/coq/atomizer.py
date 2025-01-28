import os
import re
from pathlib import Path
import json
from functools import reduce
from coqpyt.coq.base_file import CoqFile
from coqpyt.coq.structs import TermType
from atomization.coq.types import (
    Atomizer,
    Atoms,
    Term,
    AtomBase,
    BottomAtom,
    TheoremAtom,
    NotationAtom,
    DefinitionAtom,
    InductiveAtom,
)


def elicit_objective_signature(term: Term) -> str:
    """TODO"""
    return ""


def atomize(term: Term, context: Atoms) -> AtomBase:
    match term.type:
        case TermType.THEOREM | TermType.LEMMA:
            pattern_thm_lma = r"(Theorem|Lemma)\s+(\w+)\s*:\s*(.*)"
            term_type, name, signature = re.match(
                pattern_thm_lma, term.step.short_text
            ).groups()
            return TheoremAtom(
                term_type,
                name,
                term.step.ast.range.start.line,
                signature,
                context,
                [str(x) for x in term.steps] if hasattr(term, "steps") else [],
            )
        case (
            TermType.DEFINITION
            | TermType.FIXPOINT
            | TermType.COFIXPOINT
            | TermType.FUNCTION
        ):
            text = term.step.short_text.strip()
            if ":=" not in text:
                return BottomAtom()
            
            # Split into declaration and body
            decl, body = text.split(":=", 1)
            
            # Extract term type and identifier
            words = decl.split()
            term_type = words[0]  # Definition, Fixpoint, etc.
            identifier = words[1]  # The name
            
            # Everything between the identifier and := is the signature
            signature = decl[decl.find(identifier) + len(identifier):].strip()
            
            return DefinitionAtom(
                term_type,
                identifier,
                term.step.ast.range.start.line,
                signature,
                body.strip(),
                context,
            )
        case TermType.INDUCTIVE | TermType.VARIANT | TermType.COINDUCTIVE:
            text = term.step.short_text.strip()
            if ":=" not in text:
                return BottomAtom()
            
            # Split into declaration and constructors
            decl, constructors = text.split(":=", 1)
            
            # Extract term type and identifier
            words = decl.split()
            term_type = words[0]  # Inductive, CoInductive, or Variant
            identifier = words[1]  # The name
            
            # Everything between the identifier and := is the signature
            signature = decl[decl.find(identifier) + len(identifier):].strip()
            
            return InductiveAtom(
                term_type,
                identifier,
                term.step.ast.range.start.line,
                signature,
                constructors.strip(),
                context,
            )
        case TermType.NOTATION:
            notation_pattern = re.compile(
                r"""
                (?P<type>Notation|Infix)\s+
                "(?P<identifier>[^"]+)"\s+  # Capture everything between quotes
                :=\s+
                (?P<term>\([^)]+\))        # Capture everything between parentheses
                \s*
                (?:                        # Optional group for modifiers
                    \(
                    (?P<modifiers>[^)]+)   # Capture all modifiers
                    \)
                )?
                (?:\s*:\s*(?P<scope>\w+_scope))?  # Capture scope if present
                \.?                        # Optional period at end
                """,
                re.VERBOSE,
            )

            line = term.step.short_text.strip()
            if line.startswith("Fixpoint"):
                return BottomAtom()
            mtch = notation_pattern.match(line)
            if not mtch:
                # raise ValueError(f"Could not parse notation line: {line}")
                return BottomAtom()

            # Extract basic fields
            termtype = mtch.group("type")
            identifier = mtch.group("identifier")
            trm = mtch.group("term")
            scope = mtch.group("scope")

            # Parse modifiers if present
            level = None
            format_str = None
            if mtch.group("modifiers"):
                modifiers = mtch.group("modifiers")

                # Extract level
                level_match = re.search(r"at level (\d+)", modifiers)
                if level_match:
                    level = int(level_match.group(1))

                # Extract format
                format_match = re.search(r'format\s+"([^"]+)"', modifiers)
                if format_match:
                    format_str = format_match.group(1)

            return NotationAtom(
                termtype=termtype,
                identifier=identifier,
                lineno=term.step.ast.range.start.line,
                scope=scope,
                level=level,
                term=trm,
                fmt=format_str,
                deps=[],  # Empty for notations
            )
        case _:
            """
            # TODO:
            TermType.RECORD
            TermType.CLASS
            TermType.INSTANCE
            TermType.SCHEME
            TermType.FACT
            TermType.REMARK
            TermType.COROLLARY
            TermType.PROPOSITION
            TermType.PROPERTY
            TermType.OBLIGATION
            TermType.TACTIC
            TermType.RELATION
            TermType.SETOID
            TermType.DERIVE
            TermType.EQUATION
            TermType.OTHER
            """
            return BottomAtom()


class CoqAtomizer(Atomizer):
    def atomize(self) -> Atoms:
        with CoqFile(str(self.filename)) as cf:
            cf.run()
            return [
                atomize(item, [])
                for _, item in cf.context.terms.items()
            ]

    def jsonify(self) -> str:
        atoms = self.atomize()
        return json.dumps([atom.jsonify() for atom in atoms])

    def jsonify_vlib(self) -> list:
        atoms = self.atomize()
        return reduce(lambda x, y: x + y, [atom.jsonify_vlib() for atom in atoms])


def atomize_str_vlib(content: str) -> list:
    tmp = Path("_temp.v")
    with open(tmp, "w") as f:
        f.write(content)
    atomizer = CoqAtomizer(tmp)
    jsn = atomizer.jsonify_vlib()
    os.remove(tmp)
    return jsn


def atomize_str(content: str) -> str:
    tmp = Path("_temp.v")
    with open(tmp, "w") as f:
        f.write(content)
    atomizer = CoqAtomizer(tmp)
    jsn = atomizer.jsonify()
    os.remove(tmp)
    return jsn
