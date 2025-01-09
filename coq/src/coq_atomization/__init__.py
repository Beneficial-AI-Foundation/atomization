import re
from dataclasses import dataclass
from abc import abstractmethod, ABC
from typing import Literal
from pathlib import Path
import json
from coqpyt.coq.proof_file import ProofFile
from coqpyt.coq.structs import TermType, ProofTerm, Term as CoqTerm


class AtomBase(ABC):
    @abstractmethod
    def jsonify(self) -> dict:
        pass


class BottomAtom(AtomBase):
    def jsonify(self) -> dict:
        return json.loads("null")


@dataclass
class TheoremAtom(AtomBase):
    termtype: str
    identifier: str
    lineno: int
    spec: str
    deps: list[AtomBase]
    proof: list[str]

    def __str__(self) -> str:
        return f"{self.identifier} : {self.spec} := {self.proof}"

    def jsonify(self) -> dict:
        return {
            "termtype": self.termtype,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "spec": self.spec,
            "deps": [dep.jsonify() for dep in self.deps],
            "proof": self.proof,
        }


@dataclass
class NotationAtom(AtomBase):
    termtype: str
    identifier: str
    lineno: int
    scope: str | None
    level: int | None
    term: str
    fmt: str | None
    deps: list[AtomBase]

    def jsonify(self) -> dict:
        return {
            "termtype": self.termtype,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "scope": self.scope,
            "level": self.level,
            "term": self.term,
            "fmt": self.fmt,
            "deps": [dep.jsonify() for dep in self.deps],
        }


type Term = ProofTerm | CoqTerm
type Atoms = list[AtomBase]


@dataclass
class Atomizer:
    filename: Path


def atomize(term: Term, context: Atoms) -> AtomBase:
    # print(term.step.short_text)
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
            # raise NotImplementedError
            return BottomAtom()
        case TermType.INDUCTIVE | TermType.VARIANT | TermType.COINDUCTIVE:
            pattern_inductive = r"(Inductive|Variant|CoInductive)\s+(\w+)\s*:\s*((?:\w+(?:\s+\w+)*?))\s*:=\s*((?:.|[\r\n])*)"
            term_type, name, _, defn = re.match(
                pattern_inductive, term.step.short_text
            ).groups()
            return TheoremAtom(
                term_type,
                name,
                term.step.ast.range.start.line,
                defn,
                context,
                [str(x) for x in term.steps] if hasattr(term, "steps") else [],
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
        with ProofFile(str(self.filename)) as pf:
            pf.run()
            return [
                atomize(proof, [atomize(item, []) for item in proof.context])
                for proof in pf.proofs
            ]

    def jsonify(self) -> str:
        atoms = self.atomize()
        return json.dumps([atom.jsonify() for atom in atoms])


def main() -> None:
    examples = Path("examples")
    atomizer = CoqAtomizer(examples / "minimal.v")
    print(atomizer.jsonify())
