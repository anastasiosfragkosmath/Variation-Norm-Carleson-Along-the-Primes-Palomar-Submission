#!/usr/bin/env python3
"""In-memory rejection tests for check_proof_policy.py; no Lean file is created."""

import json
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from check_proof_policy import (  # noqa: E402
    CHALLENGE_THEOREMS,
    FORBIDDEN,
    mask,
    theorem_statement,
    unique_object,
    validate_challenge_source,
    validate_config,
    validate_reports,
)


def forbidden(text: str) -> bool:
    return FORBIDDEN.search(mask(text)) is not None


class PolicyTests(unittest.TestCase):
    @staticmethod
    def challenge_source() -> str:
        return "\n\n".join(f"/-- doc with `sorry` -/\ntheorem {name} : True := by\n  sorry"
                           for name in CHALLENGE_THEOREMS)

    def test_comments_and_strings_are_masked(self):
        self.assertFalse(forbidden("/- outer /- sorry -/ still comment axiom -/\ndef x := 1"))
        self.assertFalse(forbidden("-- sorry\ndef s := \"admit\""))
        self.assertTrue(forbidden("/- c -/ theorem t : True := by sorry"))

    def test_forbidden_constructs(self):
        for text in ("theorem t : False := sorry", "axiom bad : False", "unsafe def f := 1",
                     "@[implemented_by g] def f := 1", "example : 1 = 1 := by native_decide",
                     "opaque o : Nat", "macro \"x\" : term => `(1)", "#eval 1",
                     "set_option debug.skipKernelTC true", "def f := Lean.ofReduceBool"):
            with self.subTest(text=text):
                self.assertTrue(forbidden(text))

    def test_literals_cannot_open_a_fake_string(self):
        self.assertTrue(forbidden("def q := '\"'\ntheorem bad : False := sorry\ndef z := \"x\""))
        self.assertTrue(forbidden('def q := r#"a"b"#\ntheorem bad : False := sorry'))
        self.assertTrue(forbidden("def c := '\\''\ntheorem bad : False := sorry"))
        self.assertFalse(forbidden("theorem t (h' : True) : True := h'"))
        self.assertFalse(forbidden("def s := r\"sorry\""))

    def test_more_forbidden_constructs(self):
        for text in ("example : False := by stop exact trivial",
                     "set_option maxHeartbeats 1 in #eval 1", "#exit",
                     "initialize foo : IO.Ref Nat ← IO.mkRef 0",
                     "@[command_elab foo] def f := 1", "@[tactic foo] def f := 1",
                     "@[csimp] theorem t : f = g := rfl", "simproc foo (x) := fun _ => none",
                     "local macro \"x\" : term => `(1)", "syntax \"foo\" : term"):
            with self.subTest(text=text):
                self.assertTrue(forbidden(text))

    def test_decoy_statement_in_a_comment_is_ignored(self):
        source = "/- theorem t : False := -/\ntheorem t : True := by\n  sorry\n"
        self.assertEqual(theorem_statement(source, "t", "x"), ": True")
        with self.assertRaises(ValueError):
            theorem_statement(source + "theorem t : 1 = 1 := by\n  sorry\n", "t", "x")

    def test_challenge_command_whitelist(self):
        source = self.challenge_source().replace("/-- doc with `sorry` -/\n", "")
        validate_challenge_source(source)
        for extra in ("instance : Inhabited Nat := ⟨0⟩", "attribute [simp] Nat.add_comm",
                      "notation \"𝔼\" => Nat", "variable (n : Nat)", "public import Foo"):
            with self.subTest(extra=extra), self.assertRaises(ValueError):
                validate_challenge_source(extra + "\n\n" + source)

    def test_symlinks_are_rejected(self):
        import os
        import tempfile
        import check_proof_policy as policy
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "real").mkdir()
            (root / "real" / "A.lean").write_text("module\n")
            os.symlink(root / "real", root / "linked")
            saved, policy.ROOT = policy.ROOT, root
            try:
                with self.assertRaises(ValueError):
                    policy.lean_sources()
            finally:
                policy.ROOT = saved

    def test_aesop_rule_attribute_is_not_unsafe_code(self):
        self.assertFalse(forbidden("@[aesop (rule_sets := [finiteness]) unsafe 80% apply]\n"
                                   "lemma l : True := trivial"))
        self.assertFalse(forbidden("@[aesop unsafe apply] lemma l : True := trivial"))

    def test_unterminated_comment(self):
        with self.assertRaises(ValueError):
            mask("/- never closed")

    def test_challenge_placeholders_are_the_target_bodies(self):
        source = self.challenge_source()
        validate_challenge_source(source)
        name = next(iter(CHALLENGE_THEOREMS))
        for bad in (
            source.replace(f"theorem {name} : True := by\n  sorry",
                           f"theorem {name} : True := by\n  trivial\n\nsorry"),
            source + "\n\ntheorem extra : True := by\n  sorry",
            source + "\n\naxiom extra : False",
        ):
            with self.subTest(bad=bad[-40:]), self.assertRaises(ValueError):
                validate_challenge_source(bad)

    def test_statement_extraction(self):
        source = "theorem t :\n    ∀ n : ℕ, n = n := by\n  sorry\n"
        self.assertEqual(theorem_statement(source, "t", "x"), ":\n    ∀ n : ℕ, n = n")
        with self.assertRaises(ValueError):
            theorem_statement(source, "u", "x")

    def test_permitted_config(self):
        validate_config({"permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
                         "enable_nanoda": True})

    def test_forbidden_configs(self):
        for config in ({"permitted_axioms": ["sorryAx"], "enable_nanoda": True},
                       {"permitted_axioms": "propext", "enable_nanoda": True},
                       {"permitted_axioms": [], "enable_nanoda": False},
                       {"permitted_axioms": []},
                       {"permitted_axioms": [], "enable_nanoda": True, "extra": 1}):
            with self.subTest(config=config), self.assertRaises(ValueError):
                validate_config(config)

    def test_duplicate_json_key(self):
        with self.assertRaises(ValueError):
            json.loads('{"permitted_axioms": ["sorryAx"], "permitted_axioms": []}',
                       object_pairs_hook=unique_object)

    def test_standard_reports(self):
        validate_reports("'a' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
                         "'b' does not depend on any axioms\n", ["a", "b"])

    def test_bad_reports(self):
        for output in ("", "'a' depends on axioms: []\n" * 2,
                       "'other' depends on axioms: []\n", "unrecognized",
                       "'a' depends on axioms: [propext, sorryAx]\n",
                       "'a' depends on axioms: [Lean.ofReduceBool]\n"):
            with self.subTest(output=output), self.assertRaises(ValueError):
                validate_reports(output, ["a"])


if __name__ == "__main__":
    unittest.main()
