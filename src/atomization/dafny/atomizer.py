from atomization.dafny.parser import parse_dafny


def atomize_dafny(content: str) -> list:
    """Analyze a Dafny file and return its code, spec, and proof components."""
    try:

        parsed_dafny = parse_dafny(content)
        return parsed_dafny

    except Exception as e:
        print(f"Debug - Exception details: {type(e).__name__}: {str(e)}")
        raise Exception(f"Error analyzing {content}: {str(e)}")
