from abc import ABC, abstractmethod
from dataclasses import dataclass
from pathlib import Path
import json
from coqpyt.coq.structs import ProofTerm, Term as CoqTerm


class AtomBase(ABC):
    @abstractmethod
    def jsonify(self) -> dict:
        pass

    @abstractmethod
    def jsonify_vlib(self) -> list:
        pass


class BottomAtom(AtomBase):
    def jsonify(self) -> dict:
        return json.loads("null")

    def jsonify_vlib(self) -> list:
        return [self.jsonify()]


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

    def jsonify_vlib(self) -> list:
        return [
            {"content": self.spec, "type": "spec", "order": self.lineno},
            {"content": "".join(self.proof), "type": "proof", "order": self.lineno},
        ]


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

    def jsonify_vlib(self) -> list:
        return []


@dataclass
class DefinitionAtom(AtomBase):
    termtype: str
    identifier: str
    lineno: int
    signature: str
    code: str
    deps: list[AtomBase]

    def jsonify(self) -> dict:
        return {
            "termtype": self.termtype,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "signature": self.signature,
            "code": self.code,
            "deps": [dep.jsonify() for dep in self.deps],
        }

    def jsonify_vlib(self) -> list:
        return [
            {"content": self.signature, "type": "spec", "order": self.lineno},
            {"content": self.code, "type": "code", "order": self.lineno},
        ]


@dataclass
class InductiveAtom(AtomBase):
    termtype: str  # Inductive, CoInductive, or Variant
    identifier: str
    lineno: int
    signature: str  # The type (e.g., "Set" or "Type")
    constructors: str  # The constructor definitions
    deps: list[AtomBase]

    def jsonify(self) -> dict:
        return {
            "termtype": self.termtype,
            "identifier": self.identifier,
            "lineno": self.lineno,
            "signature": self.signature,
            "constructors": self.constructors,
            "deps": [dep.jsonify() for dep in self.deps],
        }

    def jsonify_vlib(self) -> list:
        return [
            {"content": self.signature, "type": "spec", "order": self.lineno},
            {
                "content": self.constructors,
                "type": "constructors",
                "order": self.lineno,
            },
        ]


type Term = ProofTerm | CoqTerm
type Atoms = list[AtomBase]


@dataclass
class Atomizer:
    filename: Path
