"""Use either archived Farkas search routine with the local parity model."""
import sys

from odd_flag_experiments import system_for


def main():
    if "--penalty" in sys.argv:
        from fit_farkas_penalty import run

        sys.argv.remove("--penalty")
    else:
        from fit_farkas_ray import run
    # Search only. The archived verifier still checks the complete exact
    # parity system and all recorded multipliers.
    run.__globals__["build_system"] = system_for
    run()


if __name__ == "__main__":
    main()
