FROM haskell:9.10.1

LABEL author="Claire Stokka"
LABEL contact="claire@clairradiant.com"
LABEL description="Versioned Agda environment for CSE3000 Research Project"
LABEL license="MIT"

# Agda needs some dependencies
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
        zlib1g-dev \
        libncurses5-dev

# Install Agda
RUN cabal update && \
    cabal install Agda-2.7.0.1

# Install Agda standard library
RUN mkdir -p /root/.agda/lib
WORKDIR /root/.agda/lib
RUN curl -L -o agda-stdlib.tar.gz https://github.com/agda/agda-stdlib/archive/v2.2.tar.gz \
    && tar -zxvf agda-stdlib.tar.gz \
    && cd agda-stdlib-2.2 \
    && cabal install \
    && mkdir -p $(agda --print-agda-app-dir) \
    && echo "/root/.agda/lib/agda-stdlib-2.2/standard-library.agda-lib" > $(agda --print-agda-app-dir)/libraries

