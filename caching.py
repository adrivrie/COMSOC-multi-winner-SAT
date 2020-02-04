from __future__ import print_function
from functools import wraps
import os
import pickle
import inspect

CACHE_ON = True

def cache(cachefile, directory="./caches/"):
    """
    A function that creates a decorator which will use "cachefile" for caching the results of the decorated function "fn".
    """
    def decorator(fn):  # define a decorator for a function "fn"
        @wraps(fn)
        def wrapped(*args, **kwargs):   # define a wrapper that will finally call "fn" with all arguments

            # if cache directory does not yet exist, create it
            if not os.path.isdir(directory):
                os.mkdir(directory)
                print(" created caching directory {}".format(directory))

            # if cache exists -> load it and return its content
            # except if contents of function have changed
            if os.path.exists(directory+cachefile):
                with open(directory+cachefile, 'rb') as cachehandle:
                    contents = pickle.load(cachehandle)
                    if CACHE_ON and contents[1] == inspect.getsource(fn):
                        print("Using cached result from '%s'" % (directory+cachefile))
                        return contents[0]

            # execute the function with all arguments passed
            res = fn(*args, **kwargs)

            # write to cache file
            if CACHE_ON:
                with open(directory+cachefile, 'wb') as cachehandle:
                    print("saving result to cache '%s'" % (directory+cachefile))
                    pickle.dump((res, inspect.getsource(fn)), cachehandle)

            return res

        return wrapped

    return decorator
