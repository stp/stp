# -----------------------------------------------------------------------------
# Setup python module in build directory
# -----------------------------------------------------------------------------
get_target_property(LIBSTP_PATH libstp LOCATION)
configure_file(library_path.py.in library_path.py @ONLY)

# Copy rest of files to build directory
configure_file(stp.py stp.py COPYONLY)
configure_file(__init__.py __init__.py COPYONLY)
